#!/bin/bash

if [ -n "$1" ]
then
pre=$1
else
pre=`ghc --print-libdir | sed -e 's+/lib/.*++g'`
fi

cabal install aterm xml fgl HTTP haskell-src -p -O --enable-documentation --global --prefix=$pre
