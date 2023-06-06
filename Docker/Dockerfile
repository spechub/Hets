FROM ubuntu:20.04

ENV LANG C.UTF-8

RUN apt-get update && apt-get install software-properties-common -y
RUN apt-add-repository ppa:hets/hets
RUN apt-get update && apt-get install -y hets-server hets-libs libatomic1 && rm -rf /var/lib/apt/lists/*

RUN mkdir /data/

WORKDIR /data/

COPY docker-entrypoint.sh /usr/local/bin/

ENTRYPOINT [ "/usr/local/bin/docker-entrypoint.sh" ]

CMD ["hets-server", "--server"]
