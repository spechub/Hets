#!/usr/local/bin/bash

PA=$1
SET=$2
ANNOS=../../Common/test/Standard.annos

. ../../Common/test/checkFunctions.sh

for i in *.hascasl
do
  echo "processing $i"
  runchecker "analysis" $i $i.output
done
