#!/usr/local/bin/bash

PA=$1
SET=$2
ANNOS=../../Common/test/Empty.annos

. ../../Common/test/checkFunctions.sh

for i in *.annos Annotations.casl
do
  echo "processing $i"
  runchecker "Annotations" $i $i.output1
  runchecker "Annos" $i $i.output2
done

for j in MixIds
do
    i=`basename $j .casl`
    runmycheck $i casl
    runwrongcheck $i casl
done
