#!/usr/local/bin/bash

PA=$1
SET=$2
ANNOS=../../Common/test/Standard.annos

. ../../Common/test/checkFunctions.sh

runchecker MixIds ../../Common/test/MixIds.casl MixIds.casl.output
runchecker MixIds ../../Common/test/WrongMixIds.casl WrongMixIds.casl.output
runchecker BasicSpec ../../CASL/test/BasicSpec.casl BasicSpec.casl.output

for i in Kinds Types Terms Items
do
    runmycheck $i hascasl
    runwrongcheck $i hascasl
done

runchecker BasicSpec BasicSpec.hascasl BasicSpec.hascasl.parser.output
runwrongcheck BasicSpec hascasl

for i in [A-HL-SX-Z]*.hascasl
do
  echo "processing $i"
  runchecker "analysis" $i $i.output
done
