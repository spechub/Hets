#!/bin/sh

#first parameter is executable
#second parameter resets ouput files

PA=$1
SET=$2

. ../../Common/test/checkFunctions.sh

runtranslate ()
{
   runcheck $PA $1 $1 $1 $1.hs $SET
}

for i in [A-Z]*.hascasl; 
do
    ../../HasCASL/hacapa analysis < $i > $i.output
    runtranslate $i
    ghc -c -Wall $i.hs > $i.out 2>&1
done
rm -f *.o *.hi
