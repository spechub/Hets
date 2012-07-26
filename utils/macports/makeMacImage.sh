#/bin/sh -x
if [ -z "$1" ] ; then
  VERSION=`date +%F`
else
  VERSION=$1
fi
IMAGE=Hets-$VERSION.dmg
/Users/Shared/maeder/Platypus-4.7/Platypus.app/Contents/Resources/platypus_clt \
 -P ../Hets/utils/macports/hets.platypus Hets.app
cp hets Hets.app/Contents/Resources/
cp -r /Users/Shared/maeder/uDrawGraph-3.1 Hets.app/Contents/Resources/
tar zxf /home/www.informatik.uni-bremen.de/cofi/Libraries/daily/lib.tgz \
 -C Hets.app/Contents/Resources
hdiutil create -srcfolder Hets.app $IMAGE
cp $IMAGE /home/www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/intel-mac/dmgs/

