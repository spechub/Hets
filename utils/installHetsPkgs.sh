#!/bin/bash

if [ -n "$1" ]
then
pre=$1
else
pre=`ghc --print-libdir | sed -e 's+/lib/.*++g'`
fi

for p in \
 mtl-1.1.1.0 \
 parsec-2.1.0.1 \
 network-2.2.1.8 \
 fgl-5.4.2.3 \
 xml-1.3.7 \
 zlib-0.5.2.0 \
 HTTP-4000.0.9 \
 cabal-install-0.8.2 \
 tar-0.3.1.0 \
 haskell-src-1.0.1.3
do ./installPkg.sh $p $pre
done
