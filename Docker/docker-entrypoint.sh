#!/usr/bin/env bash

if [ "$1" = 'hets-server' ] && [ "$3" = "--database-config=/etc/hets_db_postgresql.yml" ]; then
    echo "default: &default
  adapter: postgresql
  username: $(cat $POSTGRES_USERNAME)
  password: $(cat $POSTGRES_PASSWORD)
  host: $POSTGRES_HOST
  port: $POSTGRES_PORT
  pool: 10

production:
  <<: *default
  database: hets" > /etc/hets_db_postgresql.yml
fi

exec "$@"
