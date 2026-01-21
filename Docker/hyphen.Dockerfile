
FROM ubuntu:22.04

RUN apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y git python3-dev ghc-dynamic ghc python3 python3-pip

RUN git clone https://github.com/tbarnetlamb/hyphen.git /hyphen

RUN apt-get install -y libghc-ghc-paths-dev libghc-parser-combinators-dev libghc-unordered-containers-dev

WORKDIR /hyphen
RUN python3 hyphen/build-extn.py

RUN echo '[project]\n\
name = "hyphen"\n\
version = "0.1.0.0"\n\
\n\
[tool.setuptools]\n\
packages = [ "hyphen" ]\n\
\n\
[tool.setuptools.package-data]\n\
"*" = [ "hslowlevel.*" ]\n' > /hyphen/pyproject.toml

RUN python3 -m pip install --upgrade pip setuptools

RUN python3 -m pip install /hyphen

