#!/usr/local/bin/bash

#first parameter is executable
#second parameter resets ouput files

PA=$1
SET=$2

. checkFunctions.sh

#extra test
runchecker Terms MixIds.casl MixIds.casl.asTerms.output
runchecker Terms WrongMixIds.casl WrongMixIds.casl.asTerms.output
runchecker MixfixTerms Terms.casl Terms.casl.asMixfixTerms.output
runchecker MixfixFormula Formula.casl Formula.casl.asMixfixFormula.output

#don't take files starting with "Wrong"
for j in [A-V]*.casl; 
do
    i=`basename $j .casl`
    runmycheck $i casl
    runwrongcheck $i casl
done


