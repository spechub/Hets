#!/bin/bash

test_files=$(cat $(dirname $0)/hets-lib-testfiles)

export DATABASE_CONFIG=${DATABASE_CONFIG:-Persistence/database_postgresql.yml}
echo DATABASE_CONFIG=$DATABASE_CONFIG

set -ex

for i in $test_files
do
  $(dirname $0)/hets-lib-database-reset.sh
  hets --quiet -a none --output-types=db --database-config=$DATABASE_CONFIG --database-subconfig=test $HETS_LIB/$i
done
