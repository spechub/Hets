#!/usr/local/bin/bash

PA=$1
SET=$2

. ../CASL/checkFunctions.sh

for i in Types Terms Items;
do
    runmycheck $i hascasl
    runwrongcheck $i hascasl
done

for i in MixIds BasicSpec;
do
    runmycheck $i hascasl
done

for i in test/*.hascasl
do
  echo "processing $i"
  runchecker "analysis" $i $i.output
done
