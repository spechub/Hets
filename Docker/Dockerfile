FROM ubuntu:18.04

ENV LANG C.UTF-8

RUN apt-get update && apt-get install software-properties-common -y
RUN apt-add-repository ppa:hets/hets
RUN apt-get update && apt-get install -y hets-server hets-libs libatomic1 && rm -rf /var/lib/apt/lists/*

RUN mkdir /data

# These values need to be partially altered when running in production
ENV POSTGRES_USERNAME postgres
ENV POSTGRES_PASSWORD postgres
ENV POSTGRES_HOST localhost
ENV POSTGRES_PORT 5432

VOLUME /data

WORKDIR /data

COPY docker-configure.sh /usr/local/bin/

RUN /usr/local/bin/docker-configure.sh

EXPOSE 8000

CMD ["hets-server", "--server", "--database-config=/data/database_postgresql.yml", "--database-subconfig=development"]
