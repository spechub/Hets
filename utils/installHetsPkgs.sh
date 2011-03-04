#!/bin/bash

if [ -n "$1" ]
then
pre=$1
else
pre=`ghc --print-libdir | sed -e 's+/lib/.*++g'`
fi

#installing the binaries
BINARIES="alex gtk2hsC2hs gtk2hsHookGenerator gtk2hsTypeGen"
if which $BINARIES &> /dev/null; then
    echo Binaries already installed
else
    echo Installing binaries...
    cabal install alex gtk2hs-buildtools
fi

#installing the libraries
echo Installing libraries...
cabal install aterm xml fgl HTTP haskell-src tar glade haskeline \
              hexpat wai-extra-0.2.4.2 uni-uDrawGraph \
              -O --enable-documentation --global --prefix=$pre
