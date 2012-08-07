#!/bin/bash

# ISABELLE_BIN_PATH (if isabelle is not located in PATH)

SCRIPT=$(readlink -f $0)
SCRIPTPATH=`dirname $SCRIPT`

if [ -z $1 ]; then
 echo "Nothing to translate!"
 exit 1
fi

TRANS=$(readlink -f $1)
TRANS_T=$(basename $TRANS .thy)
TRANS=$(dirname $TRANS)/$TRANS_T

if [ ! -r $TRANS.thy ]; then
 echo "Cannot read file $TRANS.thy"
 exit 1
fi

if [ ! -z $ISABELLE_BIN_PATH ]; then
 ISABELLE="$ISABELLE_BIN_PATH/isabelle"
 if [ ! -e $ISABELLE ]; then
  echo "Cannot find isabelle executable. Maybe you didn't specify ISABELLE_BIN_PATH correctly?"
 fi
else
 if which isabelle > /dev/null ; then
   ISABELLE=`which isabelle`
 else
  echo "Cannot find isabelle executable. Maybe you need to specify ISABELLE_BIN_PATH?"
  exit 1
 fi
fi

if [ ! -x $ISABELLE ]; then
 echo "$ISABELLE is not executable"
 exit 1
fi

echo $ISABELLE

(
 echo "theory IsaExport"
 echo "imports \"$TRANS\" Wellfounded"
 echo "uses \"$SCRIPTPATH/export_helper.ml\""
 echo "begin"
 echo "ML {*"
 echo "val T = Thy_Info.get_theory \"$TRANS_T\";

val l =List.filter (String.isPrefix (Context.theory_name T))
                      (Locale.all_locales T);

List.map (Locale.params_of T) l;

val (_,tb) = Locale.locale_deps T;

val tb_list = List.map (fn (k,t) => (k,Symtab.dest t)) (Symtab.dest tb);

val parents = List.foldl (fn ((s,l),t') => List.foldl (fn ((s1,l1),t) =>
 Symtab.map_default (s1,([],[])) 
 (fn (parents,pfixes) => (s::parents,(
 ((List.map (fn Free (s,_) => s)) o List.concat) l1)@pfixes)) t
) t' l) Symtab.empty tb_list;

val l = \"Locale.comm_semi\";

val filter = [l^\"_axioms.intro\",
              l^\"_axioms_def\",
              l^\"_def\",
              l^\".intro\",
              l^\".axioms_\"];

val t = List.filter (fn t => String.isPrefix \"Locale.comm_semi\" (#1 t)) (Global_Theory.all_thms_of T);

val pretty = Pretty.str_of o (Syntax.pretty_term @{context});

List.map (fn (s,t) => (s,(pretty o (fn Const (\"==>\",_) $ _ $ t => t) o Thm.prop_of) t)) (List.filter (fn x => not (List.exists (fn y => String.isPrefix y (#1 x)) filter)) t);

val axs = List.map (pretty o (ExportHelper.strip_hol_all [] true)) ((ExportHelper.unfold_hol_conjunction o (fn _ $ _ $ tm => tm) o Thm.prop_of o #2 o Option.valOf) (List.find (fn x => #1 x = l^\"_axioms_def\") t));

dd;

val xml = ExportHelper.tinfo2xml T \"$TRANS_T\"
           (ExportHelper.theory_info T);

File.write (Path.explode \"$TRANS.isa\") (XML.string_of xml);
"
 echo "*}"
 echo "end;"

) | ($ISABELLE tty)
