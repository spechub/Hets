#!/usr/local/bin/bash

#first parameter is executable
#second parameter resets ouput files

PA=$1
SET=$2
ANNOS=../Common/test/Empty.annos

. ../Common/test/checkFunctions.sh

. ./checkFunctions.sh


for j in *.hs; 
do
    runmycheck $j hs
done


