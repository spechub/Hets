#!/bin/sh

#first parameter is executable
#second parameter resets ouput files

PA=$1
SET=$2

. ../../../Common/test/checkFunctions.sh

runhatch ()
{
   runcheck $PA $1 $1 $1 $1.out $SET
}
for i in [A-Z]*.hs; 
do
    runhatch $i
done
