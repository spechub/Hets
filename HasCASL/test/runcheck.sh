#!/bin/sh

PA=$1
SET=$2
ANNOS=../../Common/test/Standard.annos

. ../../Common/test/checkFunctions.sh

runchecker MixIds ../../Common/test/MixIds.casl MixIds.casl.output
runchecker MixIds ../../Common/test/WrongMixIds.casl WrongMixIds.casl.output
runchecker BasicSpec ../../CASL/test/BasicSpec.casl BasicSpec.casl.output
runchecker MixfixTerms ../../CASL/test/MixfixTerms.casl MixfixTerms.casl.output
runchecker MixfixTerms ../../CASL/test/MixfixFormula.casl MixfixFormula.casl.output

for i in Kinds Types Terms Items MixfixTerms
do
    runmycheck $i hascasl
    runwrongcheck $i hascasl
done

runchecker BasicSpec BasicSpec.hascasl BasicSpec.hascasl.parser.output
runwrongcheck BasicSpec hascasl

for i in [A-HLN-SX-Z]*.hascasl
do
  echo "processing $i"
  runchecker "analysis" $i $i.output
done
