FROM spechub2/hyphen:22.04 as base

ENV TZ Europe/Berlin
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
ENV HETS_LIB /opt/Hets-lib

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
      ghc>=7.10.3 happy haskell-stack\
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
      libghc-heap-dev


FROM base as build-lib

RUN apt-get -y install git
# Get source
# RUN git clone --branch 2109_python_gui https://github.com/spechub/Hets.git /opt/hets
## Alternatively copy local files.
COPY ./ /opt/hets
WORKDIR /opt/hets/
# Build and install haskell library
RUN make derived
RUN runhaskell Setup.hs configure \
      --ghc --prefix=/ \
      --disable-executable-stripping \
      --disable-benchmarks \
      --libdir=/lib/haskell-packages/ghc/lib/x86_64-linux-ghc-8.6.5 \
      --dynlibdir=/lib/haskell-packages/ghc/lib/x86_64-linux-ghc-8.6.5 \
      --libsubdir=hets-api-0.100.0 \
      --datadir=share \
      --datasubdir=hets-api \
      --haddockdir=/lib/ghc-doc/haddock/hets-api-0.100.0 \
      --docdir=share/doc/hets-api-doc \
      --package-db=/var/lib/ghc/package.conf.d \
      --disable-profiling \
      lib:Hets
RUN runhaskell Setup.hs build -j$(nproc) lib:Hets
RUN runhaskell Setup.hs copy --destdir=/tmp/hets-pkg
RUN runhaskell Setup.hs register --gen-script
RUN mv register.sh /tmp/install-hets.sh
RUN tar -czf /tmp/hets.tar.gz -C /tmp/hets-pkg/ .

FROM build-lib AS debug
WORKDIR /opt/hets
RUN runhaskell Setup.hs install
RUN \
   apt-get update && \
   apt-get install -y cvc-47 darwin eprover fact++ maude minisat pellet spass vampire yices z3 zchaff && \
   git clone https://github.com/spechub/Hets-lib.git ${HETS_LIB}

ENV PYTHONPATH=/opt/hets/python/api/src


FROM base
COPY --from=build-lib /tmp/hets.tar.gz /tmp/hets.tar.gz
COPY --from=build-lib /tmp/install-hets.sh /tmp/install-hets.sh
# RUN tar -tzf /tmp/hets.tar.gz && ls -l /bin /bin/sh && false
RUN tar -xzkpom -C / -f /tmp/hets.tar.gz
RUN /tmp/install-hets.sh

# Install provers and Hets-lib
RUN \
   apt-get update && \
   apt-get install -y cvc-47 darwin eprover fact++ maude minisat pellet spass vampire yices z3 zchaff && \
   git clone https://github.com/spechub/Hets-lib.git ${HETS_LIB}
# Install python library

COPY --from=build-lib /opt/hets/python/api /opt/hets/python/api
RUN   python3 -m pip install /opt/hets/python/api
# Add non-root user and cleanup
RUN \
   useradd -ms /bin/bash -u 921 hets && \
   rm -rf /opt/hets

WORKDIR /home/hets

USER hets
