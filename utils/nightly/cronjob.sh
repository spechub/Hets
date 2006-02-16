#!/bin/bash -xe

makeUni ()
{
date
rm -rf uni
cvs -d \
   :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository co $* uni
cd uni
./configure
$MAKE boot
\time -v $MAKE packages
./runhaddock.sh
cd ..
date
}

makeProgramatica ()
{
date
rm -rf programatica
mkdir programatica
cd programatica
lndir /home/cofi/programatica
cd ..
date
}

makeHets ()
{
date
rm -rf HetCATS
cvs -d :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository \
    co -P HetCATS 
cd HetCATS
time $MAKE
time $MAKE check
$MAKE release
date
(cd HetCATS; time $MAKE)
cd ..
}

makeLibCheck ()
{
rm -rf CASL-lib
cvs -d \
   :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository co -P CASL-lib
cd CASL-lib
mv ../HetCATS/HetCATS/hets .
date
time ./hets -v5 -o env,thy,th,dfg,pp.het,pp.tex Basic/*.casl
date
for i in HasCASL/*.het; do ./hets -v2 -o env,th,pp.het,pp.tex $i; done
date
for i in Modal/*.het; do ./hets -v2 -o env,th,pp.het,pp.tex $i; done
date
for i in CoCASL/*.het; do ./hets -v2 -o env,th,pp.het,pp.tex $i; done
date
for i in TestSuite/Correct/*.casl; do ./hets -v2 -o env,th,pp.het,pp.tex $i; done
date
cd ..
}
