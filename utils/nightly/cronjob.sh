#!/bin/bash -xe

GHCRTS='-H300m -M1g'
export GHCRTS

hetsdir=\
/home/www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets
destdir=$hetsdir/src-distribution/daily
outtypes=env,thy,th,dfg,dfg.c,pp.het,pp.tex

export hetsdir
export destdir
export outtypes

unset LANG

makeUni ()
{
date
rm -rf uni
svn co https://svn-agbkb.informatik.uni-bremen.de/uni/trunk uni
cd uni
./configure
time $MAKE cabal
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
time $MAKE
time $MAKE check
$MAKE release
date
(cd Hets; $MAKE depend; time $MAKE)
cd ..
}

latexBasicLibraries ()
{
\cp ../Hets/utils/hetcasl.sty .
pdflatex Basic-Libraries
}

checkCASLAsHasCASL ()
{
date
for i in Basic/*.casl; do ./hets -v2 -l HasCASL -o th,pp.het,pp.tex $i; done
latexBasicLibraries
date
for i in Basic/*.pp.het; do ./hets -v2 -l HasCASL -o pp.het,pp.tex $i; done
\ls -l Basic/*.pp.*
\rm -f Basic/*.pp.*
}

checkBasicCASL ()
{
date
for i in Basic/*.casl; do ./hets -v2 -o $outtypes $i; done
date
for i in Basic/*.pp.het; do ./hets -v2 -o pp.het,pp.tex $i; done
\ls -l Basic/*.pp.*
}

checkUserManual ()
{
date
for i in UserManual/*.casl; do ./hets -v2 -o $outtypes $i; done
}

reCheckBasicCASLThs ()
{
date
for i in Basic/*.th; do ./hets -v2 -o th,pp.het $i; done
}

checkHasCASL ()
{
date
for i in HasCASL/*.het HasCASL/Metatheory/*.het;
    do ./hets -v2 -o env,th,prf,pp.het,pp.tex $i; done
pdflatex HasCASL/Metatheory/HasCASL-Metatheory-Libraries.tex
}

makeLibCheck ()
{
rm -rf Hets-lib
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets-lib/trunk Hets-lib
cd Hets-lib
mv ../Hets/Hets/hets .
checkCASLAsHasCASL
checkBasicCASL
checkUserManual
reCheckBasicCASLThs
checkHasCASL
date
cd ..
}

installHetsBinary ()
{
chmod 775 hets
chgrp wwwbkb hets
bzip2 -k hets
\cp -fp hets.bz2 $hetsdir/$1/daily/
}

copyStyForCgi ()
{
\cp -f ../Hets/utils/hetcasl.sty \
  /home/www.informatik.uni-bremen.de/cofi/hets-tmp/
}

createLogFiles ()
{
cat */*.th > ../th.log
cat */*.pp.het > ../pp.log
}

runIsaBasic ()
{
../Hets/utils/nightly/runisabelle.sh Basic/*.thy > ../isa.log 2>&1
fgrep \*\*\* ../isa.log
}

runSPASSBasic ()
{
../Hets/utils/nightly/runSPASS.sh Basic/*.dfg > ../spass.log 2>&1
}
