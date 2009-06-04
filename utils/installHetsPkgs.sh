#!/bin/bash

if [ -n "$1" ]
then
for p in \
 curl-1.3.5 \
 tagsoup-0.6 \
 hxt-8.2.0 \
 HTTP-3001.1.5 \
 hxt-filter-8.2.0 \
 fgl-5.4.2.2 \
 xml-1.3.4 \
 dataenc-0.13.0.0 \
 tabular-0.1.0.2 \
 zlib-0.5.0.0 \
 HTTP-4000.0.7 \
 cabal-install-0.6.2 \
 HaXml-1.13.3 \
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
