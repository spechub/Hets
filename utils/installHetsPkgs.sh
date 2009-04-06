#!/bin/bash

if [ -n "$1" ]
then
for p in \
 curl-1.3.4 \
 tagsoup-0.6 \
 hxt-8.2.0 \
 HTTP-3001.1.4 \
 hxt-filter-8.2.0 \
 time-1.1.2.3 \
 fgl-5.4.2.2 \
 xml-1.3.3 \
 dataenc-0.12 \
 tabular-0.1.0.2 \
 zlib-0.5.0.0 \
 HTTP-4000.0.4 \
 cabal-install-0.6.2 \
 HaXml-1.13.3 \
 tar-0.3.0.0 \
 Shellac-0.9.5 \
 Shellac-editline-0.9.5
do ./installPkg.sh $p $1
done
else
echo "usage: $0 prefix"
fi
