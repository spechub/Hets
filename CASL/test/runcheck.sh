#!/bin/sh

#first parameter is executable
#second parameter resets ouput files

PA=$1
SET=$2
ANNOS=../../Common/test/Standard.annos

. ../../Common/test/checkFunctions.sh

#extra test
runchecker Terms ../../Common/test/MixIds.casl MixIds.casl.asTerms.output
runchecker Terms ../../Common/test/WrongMixIds.casl WrongMixIds.casl.asTerms.output
runchecker MixfixTerms Terms.casl Terms.casl.asMixfixTerms.output
runchecker MixfixFormula Formula.casl Formula.casl.asMixfixFormula.output

#don't take files starting with "Wrong"
for j in [A-V]*.casl; 
do
    i=`basename $j .casl`
    runmycheck $i casl
    runwrongcheck $i casl
done

for j in [X-Z]*.casl; 
do
    runchecker sentences $j $j.output
done

runchecker analysis BasicSpec.casl BasicSpec.analysis.output
runchecker signature BasicSpec.casl BasicSpec.signature.output
runchecker sentences BasicSpec.casl BasicSpec.sentences.output
