#!/bin/bash

if [ -n "$1" ]
then
for p in \
 mtl-1.1.0.2 \
 parsec-2.1.0.1 \
 network-2.2.1.7 \
 fgl-5.4.2.2 \
 xml-1.3.5 \
 html-1.0.1.2 \
 tabular-0.1.0.2 \
 zlib-0.5.2.0 \
 HTTP-4000.0.9 \
 cabal-install-0.8.2 \
 haskell-src-1.0.1.3 \
 utf8-string-0.3.6 \
 packedstring-0.1.0.1 \
 curl-1.3.5 \
 tar-0.3.1.0 \
 deepseq-1.1.0.0 \
 QuickCheck-2.1.0.3 \
 HUnit-1.2.2.1 \
 tagsoup-0.8 \
 hxt-8.5.0 \
 hxt-filter-8.4.2 \
 haskeline-0.6.2.2 \
 text-0.7.1.0 \
 parallel-2.2.0.1 \
 hexpat-0.12 \
 cgi-3001.1.7.3 \
 xhtml-3000.2.0.1 \
 stm-2.1.1.2 \
 regex-base-0.93.1 \
 regex-posix-0.94.1 \
 regex-compat-0.92
do ./installPkg.sh $p $1
done
else
echo "usage: $0 prefix"
fi
