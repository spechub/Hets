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

if [ ! -z $3 ]; then
 COMM_FILE="$3"
else
 COMM_FILE="/dev/stdin"
fi

if [ -z $1 ]; then
 echo "v0:Nothing to translate!" > $COMM_FILE
 exit 1
fi

if ! export TRANS=$(path $1); then
 echo "v0:Cannot find $1" > $COMM_FILE
 exit 1
fi

TRANS_T=$(basename $TRANS .thy)
TRANS=$(dirname $TRANS)/$TRANS_T

if [ ! -r $TRANS.thy ]; then
 echo "v0:Cannot read file $TRANS.thy" > $COMM_FILE
 exit 1
fi

if [ ! -z $2 ]; then
 OUT_FILE="$2"
else
 OUT_FILE="$TRANS.isa"
fi

if [ ! -z $ISABELLE_BIN_PATH ]; then
 ISABELLE="$ISABELLE_BIN_PATH/isabelle"
 if [ ! -e $ISABELLE ]; then
  echo "v0:Cannot find isabelle executable. Maybe you didn't specify ISABELLE_BIN_PATH correctly?" > $COMM_FILE
  exit 1
 fi
else
 if which isabelle > /dev/null ; then
   ISABELLE=`which isabelle`
 else
  echo "v0:Cannot find isabelle executable. Maybe you need to specify ISABELLE_BIN_PATH?" > $COMM_FILE
  exit 1
 fi
fi

if [ ! -x $ISABELLE ]; then
 echo "v0:$ISABELLE is not executable" > $COMM_FILE
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

echo "v1:Starting Isabelle" > $COMM_FILE

(
 echo "theory IsaExport
imports Datatype FunDef Fixrec Domain
begin
ML {*

val out' = fn (f,i,s') =>
 let val s = \"v\"^(Int.toString i)^\":\"^s'
 in case f of
   \"/dev/stdin\" => TextIO.output (TextIO.stdOut,s)
   | _ => File.write (Path.explode f) s
 end;
val out = fn (i,s) => out' (\"$COMM_FILE\",i,s);
val v = fn s => out (1,\"Isabelle: \"^s);
val e = fn s => (out (0,s); OS.Process.exit OS.Process.failure)

v \"Loading helper library\n\";
use \"$SCRIPTPATH/parser.ml\";

v \"Analyzing theory $TRANS_T\n\";

val thys = Export.xml_of_theory v \"$TRANS.thy\";

val xml = XML.Elem ((\"Export\",[]),thys);

v \"Writing theory information\n\";
(File.write (Path.explode \"$OUT_FILE\") (XML.string_of xml))
handle ex => e ((General.exnMessage ex)^\"\n\");
*}
end"
) | ($ISABELLE tty -l HOLCF) | tee $TEMP_FILE

if grep "*** Error" $TEMP_FILE &> /dev/null ; then
 echo "v0:Loading Theory failed" > $COMM_FILE
 grep "\*\*\* " $TEMP_FILE | head -n-3 > $COMM_FILE
 rm $TEMP_FILE
 exit 1
fi

rm $TEMP_FILE
