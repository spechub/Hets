#!/bin/sh -x

#change daily snapshot into a backup or release
#the first argument should be a version number or a date

INSTALLDIR=/home/www/agbkb/forschung/formal_methods/CoFI/hets
if [ -z "$1" ] ; then
  VERSION=`date +%F`
else
  VERSION=$1
fi

case `uname -s` in
  SunOS) TAR=gtar;;
  *) TAR=tar;;
esac

for i in linux linux64 pc-solaris intel-mac
do
  (cd $INSTALLDIR/$i; cp -p daily/hets.bz2 versions/hets-$VERSION.bz2)
done

(cd $INSTALLDIR/src-distribution; \
 cp -p daily/Het*.t* versions/Hets-src-$VERSION.tgz; \
 cd versions; rm -rf Hets; \
 $TAR zxf Hets-src-$VERSION.tgz)

# also unpack the new release as "recent overview of the modules"
