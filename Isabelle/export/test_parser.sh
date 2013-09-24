#!/bin/bash

# ISABELLE_BIN_PATH (if isabelle is not located in PATH)

function path() {
	if [ "${1%/*}" = "${1##*/}" ]; then
		echo $(pwd -P)/$1
        else
 		local P=`pwd`;
		cd ${1%/*} &> /dev/null && echo $(pwd -P)/${1##*/};
		local R=$?;
		cd $P &> /dev/null;
		return $R;
        fi
}

SCRIPT=$(path $0)
SCRIPTPATH=`dirname "$SCRIPT"`

if [ -z $1 ]; then
 echo "Nothing to translate!"
 exit 1
fi

if ! export TRANS=$(path $1); then
 echo "Cannot find $1"
 exit 1
fi

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
  exit 1
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

if which mktemp > /dev/null ; then
 if uname | grep Darwin &> /dev/null ; then
  TEMP_FILE=`mktemp isaexport.out`
 else
  TEMP_FILE=`mktemp`
 fi
else
 TEMP_FILE="/tmp/isaexport.out"
fi

echo "Starting Isabelle"

(
 echo "theory IsaExport
imports Datatype FunDef
begin
ML {*

use \"$SCRIPTPATH/export_helper.ml\";

val s = File.read (Path.explode \"$TRANS.thy\");

val (th,err) = Parser.scan s |> Parser.test;

File.write (Path.explode \"./test.out\") (Parser.scan s |> PolyML.makestring);

*}
end"
) | ($ISABELLE tty) | tee $TEMP_FILE

if grep "*** Error" $TEMP_FILE &> /dev/null ; then
 echo "Loading Theory failed"
 grep "\*\*\* " $TEMP_FILE | head -n-3
 rm $TEMP_FILE
 exit 1
fi

rm $TEMP_FILE
