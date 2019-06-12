#!/usr/bin/env bash

if [ "$1" = 'hets-server' ] && [ "$3" = "--database-config=/data/database_postgresql.yml" ]; then
    echo "default: &default
  adapter: postgresql
  username: $POSTGRES_USERNAME
  password: $POSTGRES_PASSWORD
  host: $POSTGRES_HOST
  port: $POSTGRES_PORT
  pool: 10

development:
  <<: *default
  database: hets_development

test:
  <<: *default
  database: hets_test

production:
  <<: *default
  database: hets" > /data/database_postgresql.yml
fi

exec "$@"
