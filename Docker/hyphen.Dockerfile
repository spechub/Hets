
FROM ubuntu:22.04

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y git python3-dev ghc-dynamic ghc python3

RUN git clone https://github.com/tbarnetlamb/hyphen.git /hyphen

RUN apt-get install -y libghc-ghc-paths-dev libghc-parser-combinators-dev libghc-unordered-containers-dev

WORKDIR /hyphen
RUN python3 hyphen/build-extn.py
RUN ln -s /hyphen/hyphen $(python3 -c 'import sysconfig; print(sysconfig.get_paths()["purelib"])')/hyphen
