#!/bin/bash

# ISABELLE_BIN_PATH (if isabelle is not located in path)

SCRIPT=$(readlink -f $0)
SCRIPTPATH=`dirname $SCRIPT`

if [ -z $1 ]; then
 echo "Nothing to translate!"
 exit 1
fi

TRANS=$(readlink -f $1)

if [ -z $HETS_ISABELLE_LIB ]; then
 echo '$HETS_ISABELLE_LIB not set!'
 exit 1
fi

if [ ! -r $TRANS.thy ]; then
 echo "Cannot read file" $TRANS
 exit 1
fi

if [ ! -z $ISABELLE_BIN_PATH ]; then
 ISABELLE_PROCESS="$ISABELLE_BIN_PATH/isabelle-process"
 if [ ! -e $ISABELLE_PROCESS ]; then
  echo "Cannot find isabelle-process executable. Maybe you didn't specify ISABELLE_BIN_PATH correctly?"
 fi
else
 ISABELLE_PROCESS=`which isabelle-process`
 if [ ! $? ]; then
  echo "Cannot find isabelle-process executable. Maybe you need to specify ISABELLE_BIN_PATH"
  exit 1
 fi
fi

if [ ! -x $ISABELLE_PROCESS ]; then
 echo "$ISABELLE_PROCESS is not executable"
 exit 1
fi

ISAPATH="/home/sternk/Isabelle2011/"

(
 echo "use \"$SCRIPTPATH/LOAD.ML\";"
 echo "ThyToOMDoc.ParseTheory \"$TRANS\";"
) | $ISABELLE_PROCESS
