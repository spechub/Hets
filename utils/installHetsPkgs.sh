#!/bin/bash

if [ -n "$1" ]
then
for p in \
 fgl-5.4.2.2 \
 xml-1.3.4 \
 tabular-0.1.0.2 \
 zlib-0.5.0.0 \
 HTTP-4000.0.7 \
 cabal-install-0.6.2 \
 HaXml-1.13.3 \
 curl-1.3.5 \
 tagsoup-0.6 \
 hxt-8.3.1 \
 hxt-filter-8.3.0 \
 tar-0.3.0.0 \
 Shellac-0.9.5 \
 utf8-string-0.3.4 \
 haskeline-0.6.1.6 \
 Shellac-haskeline-0.2
do ./installPkg.sh $p $1
done
else
echo "usage: $0 prefix"
fi
