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

val xml = ExportHelper.tinfo2xml T \"$TRANS_T\"
           (ExportHelper.theory_info T);

File.write (Path.explode \"$TRANS.isa\") (XML.string_of xml);
"
 echo "*}"
 echo "end;"

) | ($ISABELLE tty)
