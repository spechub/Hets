#!/bin/bash -xe

GHCRTS='-H300m -M1g'
export GHCRTS

makeUni ()
{
date
rm -rf uni
svn co https://svn-agbkb.informatik.uni-bremen.de/uni/trunk uni
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
rm -rf Hets
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets/trunk Hets
cd Hets
##$MAKE package_clean
time $MAKE
time $MAKE check
$MAKE release
date
(cd Hets; $MAKE depend; time $MAKE)
cd ..
}

makeLibCheck ()
{
rm -rf Hets-lib
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets-lib/trunk Hets-lib
cd Hets-lib
mv ../Hets/Hets/hets .
date
for i in Basic/*.casl; do ./hets -v2 -l HasCASL -o th,pp.het,pp.tex $i; done

\cp ../Hets/utils/hetcasl.sty .
pdflatex Basic-Libraries

date
for i in Basic/*.pp.het; do ./hets -v2 -l HasCASL -o pp.het,pp.tex $i; done
\ls -l Basic/*.pp.*
\rm -f Basic/*.pp.*

date
for i in Basic/*.casl;
    do ./hets -v2 -o env,thy,th,dfg,dfg.c,pp.het,pp.tex $i; done
date
for i in Basic/*.pp.het; do ./hets -v2 -o pp.het,pp.tex $i; done
\ls -l Basic/*.pp.*

date
for i in UserManual/*.casl;
    do ./hets -v2 -o env,thy,th,dfg,dfg.c,pp.het,pp.tex $i; done

date
for i in Basic/*.th; do ./hets -v2 -o th,pp.het $i; done

date
for i in HasCASL/*.het HasCASL/Metatheory/*.het;
    do ./hets -v2 -o env,th,prf,pp.het,pp.tex $i; done
pdflatex HasCASL/Metatheory/HasCASL-Metatheory-Libraries.tex
date
cd ..
}
