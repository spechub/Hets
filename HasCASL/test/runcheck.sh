#!/usr/local/bin/bash

PA=$1
SET=$2

. ../../CASL/checkFunctions.sh

for i in *.hascasl
do
  echo "processing $i"
  runchecker "analysis" $i $i.output
done
