FROM hyphen:20.04

ENV TZ=Europe/Berlin
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone


RUN git clone -b 1790_API https://github.com/spechub/Hets.git /hets

WORKDIR /hets

RUN apt update
RUN apt install -y software-properties-common apt-utils make
RUN apt-add-repository -y ppa:hets/hets
RUN apt update
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
 libghc-aterm-dev

ADD "https://www.random.org/cgi-bin/randbyte?nbytes=10&format=h" skipcache

RUN git pull origin
RUN make derived

RUN runhaskell Setup.hs configure --ghc --disable-profiling --disable-shared --package-db=/var/lib/ghc/package.conf.d --libdir=./Hets --disable-benchmarks lib:hets-api
RUN runhaskell Setup.hs build
RUN runhaskell Setup.hs register --gen-pkg-config=/var/lib/ghc/package.conf.d/hets-api-0.100.0

# RUN cabal install --enable-shared --verbose --package-db=/lib/ghc/package.conf.d
