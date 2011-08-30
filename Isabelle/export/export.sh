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
 ISABELLE=`which isabelle`
 if [ ! $? ]; then
  echo "Cannot find isabelle executable. Maybe you need to specify ISABELLE_BIN_PATH"
  exit 1
 fi
fi

if [ ! -x $ISABELLE ]; then
 echo "$ISABELLE is not executable"
 exit 1
fi

(
 echo "theory IsaExport"
 echo "imports \"$TRANS\" Wellfounded"
 echo "begin"
 echo "ML {*"
 echo "val T = Thy_Info.get_theory \"$TRANS_T\";
use \"$SCRIPTPATH/export_helper.ml\";
val types = ExportHelper.get_datatypes T;
val gths = ExportHelper.get_generated_theorems T types;
val consts = ExportHelper.get_consts T;
val axioms = ExportHelper.get_axioms T;
val theorems = ExportHelper.filter gths (ExportHelper.get_theorems T);
val num_consts = List.length consts;
val num_axioms = List.length axioms;
val num_theorems = List.length theorems;

(*fun contains s s1 = if String.isPrefix s s1 then true
                    else if String.size s1 = 0 then false
                         else contains s (String.extract (s1,1,NONE));

List.map #1 (List.filter ((contains \"rec\") o #1) (theorems));


val t1 = Option.valOf (Datatype.get_info T @{type_name list});
#rec_names t1;

Inductive.the_inductive (ProofContext.init_global T) \"list1_rec_set\"

val t2 = Option.valOf (Datatype.get_info T @{type_name type2});

Binding.qualify true \"test\" (Binding.name \"abc\");

val t1 = Option.valOf (#2 (List.hd types));
#alt_names t1;
#sorts t1;
Recdef.get_recdef T (Sign.intern_const T \"indicator\")*)"
 echo "*}"
 echo "end;"

 #echo "ThyToOMDoc.ParseTheory \"$TRANS\";"
) | $ISABELLE tty -p ""
