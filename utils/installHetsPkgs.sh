#!/bin/bash

if [ -n "$1" ]
then
pre=$1
else
pre=`ghc --print-libdir | sed -e 's+/lib/.*++g'`
fi

for p in \
 transformers-0.2.2.0 \
 mtl-2.0.0.0 \
 parsec-2.1.0.1 \
 network-2.2.1.10 \
 fgl-5.4.2.3 \
 xml-1.3.7 \
 zlib-0.5.2.0 \
 HTTP-4000.0.10
do ./installPkg.sh $p $pre
done
