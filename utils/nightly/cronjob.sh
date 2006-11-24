#!/bin/bash -xe

makeUni ()
{
date
rm -rf uni
cvs -d \
   :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository co $* uni
cd uni
./configure
time $MAKE packages
./runhaddock.sh
cd ..
date
}

makeProgramatica ()
{
date
rm -rf programatica
cvs -d :pserver:anoncvs@cvs.haskell.org:/cvs co -P programatica/tools/base
cvs -d :pserver:anoncvs@cvs.haskell.org:/cvs co -P programatica/tools/property
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
(cd HetCATS; $MAKE depend; time $MAKE)
cd ..
}

makeLibCheck ()
{
rm -rf CASL-lib
cvs -d \
   :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository \
   co -P CASL-lib
cd CASL-lib
mv ../HetCATS/HetCATS/hets .
date
for i in Basic/*.casl; do ./hets -v2 -o env,thy,th,dfg,pp.het,pp.tex $i; done
date
for i in HasCASL/*.het; do ./hets -v2 -o env,th,pp.het,pp.tex $i; done
date
cd ..
}
