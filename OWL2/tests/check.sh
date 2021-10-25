#!/bin/bash

# - Parser Printer (own testscripts)
#   - MS
#   - AS
#   - XML
# - Calling hets on (static analysis)
#   - DOL
#   - MS
#   - AS
#   - XML

# 1. run tests for *.xml
# 2. run tests for *.omn
ECHO="echo -e"

$ECHO "\nhi !\n"

[[ `uname -s` == 'SunOS' ]] && MAKE=gmake || MAKE=make

ALL=`ls`
ALL=". $ALL"



TESTS=$(pwd)
cd ../..
HETSROOT=$(pwd)


HETS_OWL_TOOLS=$HETSROOT/OWL2
export HETS_OWL_TOOLS

$ECHO "\ncompiling runTest...\n"

TESTSCRIPT=$HETSROOT/OWL2/scripts/runTest
${MAKE} $TESTSCRIPT


cd $TESTS
for DIR in $ALL
do
    if test -d $DIR;
        then
            $ECHO "Entering $DIR"
            cd $DIR

            $ECHO "Running Functional Syntax Files"
            for i in *.ofn
            do
                if test -f $i
                then
                    $ECHO -n "  Testing $i ... "
                    $TESTSCRIPT $i
                fi
            done

            $ECHO "Running Manchester Syntax Files"
            for i in ./*.omn
            do
                if test -f $i
                then
                    $ECHO -n "  Testing $i ... "
                    $TESTSCRIPT $i
                fi
            done

            for i in ./*.mno
            do
                if test -f $i
                then
                    $ECHO -n "  Testing $i ... "
                    $TESTSCRIPT $i
                fi
            done

            $ECHO "Running XML Syntax Files"
            for i in *.xml
            do
                if test -f $i
                then
                    $ECHO -n "  Testing $i ... "
                    $TESTSCRIPT $i
                fi
            done

            $ECHO "Running hets on all files"
            for i in *.ofn *.omn *.mno *.xml *.rdf
            do
                if test -f $i
                then
                    $ECHO "Testing $i ... "
                    $HETSROOT/hets $i
                fi
            done

    fi
done

$ECHO "\nbye bye !\n"
