

FROM spechub2/hyphen:22.04

ENV TZ=Europe/Berlin
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
ENV HETS_LIB=/opt/Hets-lib

RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone && \
   apt-get update && apt-get -y install locales && locale-gen en_US.UTF-8 && \
   apt-get install -y software-properties-common apt-utils make && \
# Install build and runtime dependencies
   apt-add-repository -y ppa:hets/hets && \
   apt-get update && \
   apt-get install -y openjdk-8-jdk-headless ant cabal-install\
      ksh perl-base tar xz-utils zip\
      libmysqlclient-dev\
      ghc-haddock libghc-missingh-dev\
      ghc>=7.10.3 happy\
      libghc-mutable-containers-dev\
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
      libghc-xeno-dev\
      libghc-heap-dev && \
# Install provers and Hets-lib
   apt-get install -y cvc-47 darwin eprover fact++ maude minisat pellet spass vampire yices z3 zchaff && \
   git clone https://github.com/spechub/Hets-lib.git ${HETS_LIB} && \
# Get source
   git clone --branch 2109_python_gui https://github.com/spechub/Hets.git /opt/hets && \
## Alternatively copy local files. Careful! Creates two additional layers
#    true
# COPY ./ /opt/hets
# RUN true && \
   cd /opt/hets/ && \
# Build and install haskell library
   make derived && \
   runhaskell Setup.hs configure \
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
      lib:Hets && \
   runhaskell Setup.hs build -j$(nproc) lib:Hets && \
   runhaskell Setup.hs install && \
# Install python library
   python3 -m pip install /opt/hets/python/api && \
# Add non-root user and cleanup
   useradd -ms /bin/bash -u 921 hets && \
   rm -rf /opt/hets

WORKDIR /home/hets

USER hets
