#!/usr/local/bin/bash

PA=$1
SET=$2

. ../CASL/checkFunctions.sh

for i in MixIds Kinds Types Terms Items BasicSpec;
do
    runmycheck $i hascasl
    runwrongcheck $i hascasl
done

i=Prelude.hascasl
echo "processing $i"
runchecker "analysis" $i $i.output

(cd test; bash runcheck.sh ../$PA $SET)
