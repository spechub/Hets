#!/bin/bash

if [ -n "$1" ]
then
for p in \
 mtl-1.1.0.2 \
 parsec-2.1.0.1 \
 network-2.2.1.7 \
 fgl-5.4.2.2 \
 xml-1.3.7 \
 zlib-0.5.2.0 \
 HTTP-4000.0.9 \
 cabal-install-0.8.2 \
 haskell-src-1.0.1.3
do ./installPkg.sh $p $1
done
else
echo "usage: $0 prefix"
fi
