#!/bin/bash

installdir=$2

case `uname -s` in
  SunOS) TAR=gtar;;
  *) TAR=tar;;
esac

if [ -n "$installdir" ]; then

pkg=`echo $1 | sed -e 's/^\(.*\)-\([0-9\.]*\)$/\1/'`
echo $pkg
ver=`echo $1 | sed -e 's/^\(.*\)-\([0-9\.]*\)$/\2/'`
echo $ver

wget http://hackage.haskell.org/packages/archive/$pkg/$ver/$1.tar.gz
$TAR zxf $1.tar.gz
cd $1
ghc --make Setup.*
../globallyInstallGhcPgk.sh ./Setup $installdir
cd ..
rm -rf $1
rm $1.tar.gz
else
echo "usage: $0 package prefix"
fi
