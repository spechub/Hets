#!/bin/sh

PA=$1
SET=$2
ANNOS=../../Common/test/Empty.annos

. ../../Common/test/checkFunctions.sh

for i in *.annos Annotations.casl
do
  echo "processing $i"
  runchecker "Annotations" $i $i.output
  runchecker "Annos" $i $i.perLine.output
  runchecker "GlobalAnnos" $i $i.global.output
done

runmycheck MixIds casl
runwrongcheck MixIds casl
runchecker SortIds MixIds.casl MixIds.casl.asSortIds.output
runchecker VarIds MixIds.casl MixIds.casl.asVarIds.output 
