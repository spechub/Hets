#/bin/sh -x
if [ -z "$1" ] ; then
  VERSION=`date +%F`
else
  VERSION=$1
fi
IMAGE=Hets-$VERSION.dmg
RES=Hets.app/Contents/Resources
/Users/Shared/maeder/Platypus-4.8/Platypus.app/Contents/Resources/platypus_clt \
 -P ../Hets/utils/macports/hets.platypus Hets.app
cp hets $RES/
cp -r /Users/Shared/maeder/uDrawGraph-3.1 $RES/
tar zxf /home/www.informatik.uni-bremen.de/cofi/Libraries/daily/lib.tgz \
 -C $RES
OWLSRC=/home/linux-bkb/hets-owl-tools
mkdir -p $RES/hets-owl-tools/lib
cp $OWLSRC/OntoDMU.jar $OWLSRC/OWL2Parser.jar $OWLSRC/OWLLocality.jar \
  $OWLSRC/hets.magic $RES/hets-owl-tools/
cp $OWLSRC/AProVE.jar.old $RES/hets-owl-tools/AProVE.jar
cp $OWLSRC/lib/*.jar $RES/hets-owl-tools/lib/
cp -RH /home/linux-bkb/pellet $RES
hdiutil create -srcfolder Hets.app -fs HFS+ $IMAGE
cp $IMAGE /home/www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/intel-mac/dmgs/
