#!/bin/bash

test_files=$(cat $(dirname $0)/hets-lib-testfiles)

set -ex
for i in $test_files
do
  hets --quiet -a none $HETS_LIB/$i
done
