#!/bin/bash

createXUpdate ()
{
f=`dirname $1`/`basename $1 .het`
hets -v2 -o xml $f
mv $f.xml $f.xh
hets -v2 -A -o xml $f
mv $f.xml $f.xhi
cp $1 $1.bak
diff -u $1 $2 > patch
patch $1 patch
hets -v2 -o xml $f
mv $f.xml $f.new.xh
cp $1.bak $1
dir=`pwd`
b2=`basename $2 .het`
pushd $HETS_GMOC
rm -f tmp/*.xupdate
bin/gmoc -c Configuration.xml -itype file moc \
  $dir/$f.xh $dir/$f.xhi $dir/$f.new.xh
mv tmp/*.xupdate $dir/$b2.xupdate
popd
}

for i in Spec.het
do
   for j in Add Remove Modify
   do
       for k in Symbol Axiom
       do createXUpdate $i $j$k$i
       done
   done
done
