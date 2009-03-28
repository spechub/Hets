#!/bin/sh -x

#link to a new release version
#the link type (2nd arg) is either "pre" or "released"  

INSTALLDIR=/home/www/agbkb/forschung/formal_methods/CoFI/hets 
VERSION=$1
LINKTYPE=$2
for i in linux solaris mac pc-solaris intel-mac linux64
do
  (cd $INSTALLDIR/$i; f=${LINKTYPE}hets.bz2; rm $f; \
   ln -s versions/hets-$VERSION.bz2 $f)
done
      
(cd $INSTALLDIR/src-distribution; \
 f=${LINKTYPE}Hets-src.tgz; rm $f; 
 ln -s versions/Hets-src-$VERSION.tgz $f)
