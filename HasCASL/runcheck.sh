#!/usr/local/bin/bash

. ../CASL/checkFunctions.sh

for i in Types Terms Items;
do
    runmycheck hacapa $i hascasl
    runwrongcheck hacapa $i hascasl
done

for i in MixIds BasicSpec;
do
    runmycheck hacapa $i hascasl
done

