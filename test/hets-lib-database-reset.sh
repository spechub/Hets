#!/bin/bash

case "$JOB" in
  "PostgreSQL")
    psql -U postgres -c 'drop database hets_test;' > /dev/null
    psql -U postgres -c 'create database hets_test;' > /dev/null
    ;;
  "MySQL")
    mysql -u root -e 'drop database if exists hets_test;'
    mysql -u root -e 'create database hets_test;'
    ;;
  "SQLite")
    rm -rf $DATABASE_FILE
    ;;
esac

case "$JOB" in
  "PostgreSQL"|"MySQL")
    hets --quiet --output-types=db --database-config=$DATABASE_CONFIG --database-subconfig=test --logic-graph 2> /dev/null
    ;;
  "SQLite")
    hets --quiet --output-types=db --database-file=$DATABASE_FILE --logic-graph 2> /dev/null
    ;;
esac
