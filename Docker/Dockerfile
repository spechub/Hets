FROM ubuntu:18.04

ENV LANG C.UTF-8

RUN apt-get update && apt-get install software-properties-common -y
RUN apt-add-repository ppa:hets/hets
RUN apt-get update && apt-get install -y hets-server hets-libs libatomic1 && rm -rf /var/lib/apt/lists/*

RUN mkdir /data/

WORKDIR /data/

# Workaround for new hets-server binary (2019-06-19)
RUN rm /usr/lib/hets/hets-server
RUN wget http://iks.cs.ovgu.de/~till/hets-server -q -P /usr/lib/hets/
RUN chmod +x /usr/lib/hets/hets-server
# End Workaround

COPY docker-entrypoint.sh /usr/local/bin/

ENTRYPOINT [ "/usr/local/bin/docker-entrypoint.sh" ]

CMD ["hets-server", "--server"]
