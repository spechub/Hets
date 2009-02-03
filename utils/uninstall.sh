#!/bin/sh -x

#remove an installed version
#the first argument should be a version number or a date  
#compute date by "date -Idate"

INSTALLDIR=/home/www/agbkb/forschung/formal_methods/CoFI/hets 
VERSION=$1
for i in linux linux64 solaris mac pc-solaris intel-mac
do
  (cd $INSTALLDIR/$i; rm versions/hets-$VERSION.bz2)
done
      
(cd $INSTALLDIR/src-distribution; rm versions/Hets-src-$VERSION.tgz) 

