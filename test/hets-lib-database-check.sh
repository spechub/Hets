#!/bin/bash

test_files=$(cat $(dirname $0)/hets-lib-testfiles)

DATABASE_FILE=${DATABASE_FILE:-/tmp/hets-lib-database-check.sqlite}
echo DATABASE_FILE=$DATABASE_FILE

set -ex

hets --output-types=db --database-file=$DATABASE_FILE --logic-graph

for i in $test_files
do
  hets --quiet -a none --output-types=db --database-file=$DATABASE_FILE $HETS_LIB/$i
done
