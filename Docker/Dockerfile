FROM ubuntu:18.04

ENV LANG C.UTF-8

RUN apt-get update && apt-get install software-properties-common -y
RUN apt-add-repository ppa:hets/hets
RUN apt-get update && apt-get install -y hets-server libatomic1 && rm -rf /var/lib/apt/lists/*

RUN mkdir /data
VOLUME /data

WORKDIR /data

EXPOSE 8000

# TODO: add Hets-lib
CMD ["hets-server", "--server"]