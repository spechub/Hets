#!/usr/local/bin/bash

#first parameter resets ouput files

. checkFunctions.sh


#extra test
runcheck capa Terms MixIds.casl MixIds.casl.output $1
runcheck capa Terms WrongMixIds.casl WrongMixIds.casl.asTerms.output $1

#don't take files starting with "Wrong"
for j in [A-V]*.casl; 
do
    i=`basename $j .casl`
    runmycheck capa $i casl $1
    runwrongcheck capa $i casl $1
done


