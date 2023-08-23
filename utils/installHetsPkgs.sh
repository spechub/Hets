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
pre=`ghc --print-libdir | sed -e 's+/lib.*/.*++g'`
fi

opts="--enable-documentation -p --global --prefix=$pre"

#    echo Installing binaries...
cabal install gtk2hs-buildtools $opts

echo Installing libraries...
cabal install aterm random utf8-string xml fgl HTTP haskeline HaXml \
              hexpat uni-uDrawGraph parsec1 wai-extra warp tar glade $opts

cabal install \
  http://theo.cs.uni-magdeburg.de/downloads/hets/src/programatica-1.0.0.5.tar.gz \
  --global --prefix=$pre

ghc-pkg hide parsec1
ghc-pkg hide programatica
