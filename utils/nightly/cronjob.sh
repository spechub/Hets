#!/bin/bash -xe

GHCRTS='-H300m -M1g'
LANG=C
LC_ALL=C
case `uname -s` in
  SunOS) TAR=gtar; MAKE=gmake;;
  *) TAR=tar; MAKE=make;;
esac

export GHCRTS
export LANG
export LC_ALL
export TAR
export MAKE


hetsdir=\
/home/www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets
destdir=$hetsdir/src-distribution/daily
outtypes=env,thy,th,dfg,dfg.c,tptp,tptp.c,pp.het,pp.tex

export hetsdir
export destdir
export outtypes

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
ant init
time $MAKE
time $MAKE check
$MAKE release
date
(cd Hets; ant init; $MAKE depend; time $MAKE)
cd ..
}

# within Hets-lib
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
\ls -sh1 Basic/*.pp.*
\rm -f Basic/*.pp.*
}

checkBasicCASL ()
{
date
for i in Basic/*.casl; do ./hets -v2 -o $outtypes $i; done
date
for i in Basic/*.pp.het; do ./hets -v2 -o pp.het,pp.tex $i; done
\ls -sh1 Basic/*.pp.*
date
for i in Examples/*.casl CASL/*.casl;  do ./hets -v2 $i; done
}

checkUserManual ()
{
date
for i in UserManual/*.casl; do ./hets -v2 -o $outtypes $i; done
}

checkCalculi ()
{
date
for i in Calculi/*/*.casl Calculi/*/*.het; do ./hets -v2 $i; done
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
if [ -z "$1" ]; then
  pdflatex HasCASL/Metatheory/HasCASL-Metatheory-Libraries.tex
fi
}

makeLibCheck ()
{
rm -rf Hets-lib
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets-lib/trunk Hets-lib
cd Hets-lib
mv ../Hets/Hets/hets .
if [ -z "$1" ]; then
  checkCASLAsHasCASL
fi
checkBasicCASL
checkUserManual
reCheckBasicCASLThs
checkHasCASL $1
date
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
fgrep "Line " ../spass.log
}

runDarwinBasic ()
{
../Hets/utils/nightly/runDarwin.sh Basic/*.tptp.c > ../darwin.log 2>&1
fgrep Fatal ../darwin.log
}

checkIsaOf ()
{
./hets -v2 -o thy $1
../Hets/utils/nightly/runisabelle.sh `dirname $1`/*.thy > ../isa$2.log 2>&1
fgrep \*\*\* ../isa$2.log
}

checkConsOf ()
{
./hets -v2 -o tptp.c $1
../Hets/utils/nightly/runDarwin.sh `dirname $1`/*.tptp.c > ../cons$2.log 2>&1
fgrep " Satisfiable" ../cons$2.log
}

checkBins ()
{
../Hets/Syntax/hetpa Basic/LinearAlgebra_II.casl

../Hets/Common/ATerm/ATermLibTest Basic/*.env
diff Basic/LinearAlgebra_II.env Basic/LinearAlgebra_II.env.ttttt

time ../Hets/Common/ATerm/ATermDiffMain Basic/LinearAlgebra_II.env \
    Basic/LinearAlgebra_II.env.ttttt
}

checkCats ()
{
cats -input=nobin -output=nobin -spec=gen_aterm Basic/SimpleDatatypes.casl
../Hets/ATC/ATCTest Basic/SimpleDatatypes.tree.gen_trm
./hets -v3 -p -i gen_trm -o pp.het Basic/SimpleDatatypes.tree.gen_trm
}

makeSources ()
{
cd ../Hets/doc
pdflatex UserGuide
bibtex UserGuide
pdflatex UserGuide
pdflatex UserGuide
cd ..
$MAKE doc
\cp doc/UserGuide.pdf docs
\cp doc/Programming-Guidelines.txt docs
\cp ../Hets-lib/Basic-Libraries.pdf docs
chgrp -R wwwbkb docs
\cp -rfp docs $destdir
gzip Hets.tar
chmod 664 Hets.tar.gz
chgrp wwwbkb Hets.tar.gz
\cp -fp Hets.tar.gz $destdir
}

checkMoreBins ()
{
Common/test_parser -p casl_id2 Common/test/MixIds.casl
Haskell/hana ToHaskell/test/*.hascasl.hs
}

runIsaHS ()
{
cd Haskell/test/HOLCF
cp ../HOL/*.hs .
../../../Haskell/h2hf hc *.hs
../../../utils/nightly/runHsIsabelle.sh *.thy > ../../../../isaHs.log 2>&1
grep "^\*\*\*" ../../../../isaHs.log
cd ../../..
}

makeCofiLib ()
{
cd /tmp
rm -rf Hets-lib
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets-lib/trunk Hets-lib
$TAR czvf lib.tgz --exclude=.svn --exclude=diplom_dw Hets-lib
chmod 664 lib.tgz
chgrp agcofi lib.tgz
\cp -fp lib.tgz /home/www.informatik.uni-bremen.de/cofi/Libraries/daily/
}

repackDocs ()
{
cd $destdir
\rm -rf Hets
$TAR zxf Hets.tar.gz
\mv docs Hets/docs
\rm -f Hets.tar.gz
$TAR zcf Hets-src.tgz Hets
}

moreChecks ()
{
cd $HETS_LIB
date
\rm Basic/*.th
for i in Basic/*.casl;
    do ./hets -v2 -o th -t CASL2SubCFOL $i; done
date
for i in Basic/*.th; do ./hets -v2 -o th,pp.het $i; done
date
\rm Basic/*.thy
for i in Basic/*.casl;
    do ./hets -v2 -o thy -t CASL2PCFOL:CASL2SubCFOL:CASL2Isabelle $i; done
date
../Hets/utils/nightly/runisabelle.sh Basic/*.thy > ../isa2.log 2>&1
fgrep \*\*\* ../isa2.log
}

checkEnvs ()
{
date
for i in */*.env; do ./hets -v2 -o prf $i; done
}

checkPrfs ()
{
date
for i in */*.prf; do ./hets -v2 -o th $i; done
}

updateOMDoc ()
{
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets-OMDoc/trunk Hets-OMDoc
cd Hets-OMDoc
make
svn diff
svn ci -m "nightly change"
}

updateLibForCgi ()
{
cd /home/cofi/Hets-lib
svn update
}
