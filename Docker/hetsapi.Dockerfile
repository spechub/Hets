FROM hyphen:20.04

ENV TZ=Europe/Berlin
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt-get update
RUN apt-get install -y software-properties-common apt-utils make
RUN apt-add-repository -y ppa:hets/hets
RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt install -y openjdk-8-jdk-headless ant cabal-install\
 ksh perl-base tar xz-utils zip\
 texlive-latex-base texlive-latex-extra texlive-fonts-recommended latexmk\
 libmysqlclient-dev\
 ghc-haddock libghc-missingh-dev\
 ghc>=7.10.3 happy\
 libghc-haxml-dev libghc-tar-dev libghc-random-dev libghc-parsec3-dev\
 libghc-fgl-dev libghc-xml-dev\
 libghc-http-dev libghc-warp-dev libghc-wai-extra-dev\
 libghc-split-dev libghc-file-embed-dev libghc-monad-logger-dev\
 libghc-yaml-dev libghc-esqueleto-dev>=2.5.3\
 libghc-persistent-dev>=2.7.0 libghc-persistent-template-dev>=2.5.2\
 libghc-persistent-postgresql-dev>=2.6.1\
 libghc-persistent-sqlite-dev>=2.6.2\
 libghc-utf8-string-dev libghc-relation-dev\
 libghc-persistent-mysql-dev\
 libghc-hexpat-dev\
 libghc-aterm-dev\
 libghc-xeno-dev


# RUN git clone -b 1790_API https://github.com/spechub/Hets.git /hets
## OR
COPY ./ /hets

WORKDIR /hets

RUN make derived

RUN runhaskell Setup.hs configure \
    --ghc --prefix=/ \
    --disable-executable-stripping \
    --disable-benchmarks \
    --libdir=/lib/haskell-packages/ghc/lib/x86_64-linux-ghc-8.6.5 \
    --libsubdir=hets-api-0.100.0 \
    --datadir=share \
    --datasubdir=hets-api \
    --haddockdir=/lib/ghc-doc/haddock/hets-api-0.100.0 \
    --docdir=share/doc/hets-api-doc \
    --package-db=/var/lib/ghc/package.conf.d \
    --disable-profiling \
    lib:Hets
RUN runhaskell Setup.hs build lib:Hets
RUN runhaskell Setup.hs install
