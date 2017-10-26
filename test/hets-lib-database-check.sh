#!/bin/bash

test_files=$(cat $(dirname $0)/hets-lib-database-testfiles)

export DATABASE_CONFIG=${DATABASE_CONFIG:-Persistence/database_postgresql.yml}
export DATABASE_FILE=${DATABASE_FILE:-/tmp/hets.sqlite}

case "$JOB" in
  "PostgreSQL"|"MySQL")
    call_hets="hets --quiet --output-types=db --database-config=$DATABASE_CONFIG --database-subconfig=test"
    ;;
  "SQLite")
    call_hets="hets --quiet --output-types=db --database-file=$DATABASE_FILE"
    ;;
esac
echo "call_hets = $call_hets"

set -ex

for i in $test_files
do
  $(dirname $0)/hets-lib-database-reset.sh
  $call_hets $HETS_LIB/$i
done
