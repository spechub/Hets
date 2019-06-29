#!/bin/bash

createXUpdate ()
{
f=`dirname $1`/`basename $1 .dol`
../../hets -v2 --relative-positions -o xml $f
mv $f.xml $f.xh
../../hets -v2 --relative-positions -A -o xml $f
mv $f.xml $f.xhi
cp $1 $1.bak
propagateDiff $1 $1 $2
../../hets -v2 --relative-positions -o xml $f
mv $f.xml $f.new.xh
cp $1.bak $1
dir=`pwd`
b2=`basename $2 .dol`
# pushd $HETS_GMOC
# rm -f tmp/*.xupdate
# rm -f tmp/*.imp
# bin/gmoc -c Configuration.xml -itype file moc \
#   $dir/$f.xh $dir/$f.xhi $dir/$f.new.xh
# mv tmp/*.xupdate $dir/$b2.xupdate
# mv tmp/*.imp $dir/$b2.imp
# popd

# cp $dir/$f.xh $dir/$f.hetsdginternxml
# cp $dir/$f.new.xh $dir/$f.new.hetsdginternxml
# pushd $HETS_GMOC2
# bin/gmoc -itype file -otype diff -o $dir/$b2.xupdate2 sdiff \
#  $dir/$f.hetsdginternxml $dir/$f.new.hetsdginternxml
# popd

../../Common/testxmldiff $dir/$f.xh $dir/$f.new.xh > $dir/$b2.xupdate3
}

propagateDiff ()
{
diff -u $1 $3 > patch
patch $2 patch
}

createUpdates ()
{
for i in Spec.dol
do
   for j in Add Remove Modify
   do
       for k in Symbol Axiom Theorem
       do createXUpdate $i $j$k$i
       done
   done
done
for i in Spec2.dol Spec3.dol
do
   for j in Add Remove
   do createXUpdate $i ${j}Node$i
   done
done
}

callHets ()
{
for i in *Spec.xupdate3
do
../../hets -v2 --relative-positions -U $i Spec.dol
cp Spec.xml $i.xml
done
for i in *Spec2.xupdate3
do
../../hets -v2 --relative-positions -U $i Spec2.dol
cp Spec2.xml $i.xml
done
for i in *Spec3.xupdate3
do
../../hets -A -v2 --relative-positions -U $i Spec3.dol
cp Spec3.xml $i.xml
done
}

## uncomment the slow createUpdates if you do not have the .xupdates files
createUpdates
callHets
