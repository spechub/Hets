
FROM ubuntu:lts

RUN apt update
RUN apt upgrade -y
RUN apt install -y git python3-dev ghc-dynamic ghc python3

RUN git clone https://github.com/tbarnetlamb/hyphen.git /hyphen

RUN apt install -y libghc-ghc-paths-dev libghc-parser-combinators-dev libghc-unordered-containers-dev

WORKDIR /hyphen
RUN python3 hyphen/build-extn.py
RUN ln -s /hyphen/hyphen /usr/local/lib/python3.8/dist-packages/hyphen
