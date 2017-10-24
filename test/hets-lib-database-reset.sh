#!/bin/bash

if [ -n "$WITH_POSTGRESQL" ]
then
  psql -U postgres -c 'drop database hets_test;' > /dev/null
  psql -U postgres -c 'create database hets_test;' > /dev/null
fi
if [ -n "$WITH_MYSQL" ]
then
  mysql -u root -e 'drop database hets_test;'
  mysql -u root -e 'create database hets_test;'
fi
hets --quiet --output-types=db --database-config=$DATABASE_CONFIG --database-subconfig=test --logic-graph 2> /dev/null
