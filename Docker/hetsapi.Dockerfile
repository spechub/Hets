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
# libghc-uni-udrawgraph-dev\
# libghc-gtk-dev

#RUN apt install -y libpcre3-dev
#RUN cabal update
#RUN sed -i '199 i \ \ \ \ , gtk' /hets/Hets.cabal
#RUN head -n 271 Hets.cabal > Hets.cabal.tmp && mv Hets.cabal.tmp Hets.cabal
RUN git pull origin
RUN make derived
#RUN cabal build hets-api
RUN cabal install --enable-shared --verbose --package-db=/lib/ghc/package.conf.d
#RUN ghc --make -dynamic -shared -fPIC -DGTKGLADE Driver/Api.hs -ohi -o libhets.so -c
