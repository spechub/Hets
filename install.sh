#!/bin/sh

#change daily snapshot into a release 
#make sure the file version_nr exists

INSTALLDIR=/home/www/agbkb/forschung/formal_methods/CoFI/hets 
VERSION=`cat version_nr`
for i in linux solaris mac
do
  (cd $INSTALLDIR/$i; cp -p daily/hets versions/hets-$VERSION;
      rm  -f hets; ln -s versions/hets-$VERSION hets)
done
      
  

