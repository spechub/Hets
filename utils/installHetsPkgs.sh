#!/bin/bash
#
#
# Note that before running this script you need:
#  - cabal-install
#  - zlib.h (zlib1g-dev or similar)
#  - curses.h (libncurses-dev or similar)
#  - cairo C lib (libcairo2-dev or similar)
#  - glib-2.0 C lib (libglib2.0-dev or similar)
#  - pango(>=1.0) C lib (libpango1.0-dev or similar)
#  - gtk-2.0 C lib (libgtk2.0-dev or similar)
#  - glade-2.0 C lib (libglade2-dev or similar)
#  - happy
#


if [ -n "$1" ]
then
pre=$1
else
pre=`ghc --print-libdir | sed -e 's+/lib/.*++g'`
fi

opts="--enable-documentation --global --prefix=$pre"

#installing the binaries
BINARIES="alex gtk2hsC2hs gtk2hsHookGenerator gtk2hsTypeGen"
if which $BINARIES &> /dev/null; then
    echo Binaries already installed
else
    echo Installing binaries...
    cabal install alex gtk2hs-buildtools $opts
fi

#installing the libraries
echo Installing libraries...
cabal install aterm random xml fgl HTTP tar glade haskeline \
              hexpat wai-extra warp uni-uDrawGraph parsec1 $opts

cabal install \
  http://www.dfki.de/sks/hets/src-distribution/programatica-1.0.0.3.tar.gz \
  --global --prefix=$pre

ghc-pkg hide parsec1
ghc-pkg hide programatica
