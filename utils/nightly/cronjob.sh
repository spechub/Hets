#!/bin/bash -xe

# GHCRTS -A300m is needed to speed up writing out aterms to detect sharing
GHCRTS='-H300m -M3g'
LANG=de_DE.UTF-8

case `uname -s` in
  SunOS) TAR=gtar; MAKE=gmake;;
  *) TAR=tar; MAKE=make;;
esac

HETS_OWL_TOOLS=/home/linux-bkb/hets-owl-tools
HETS_ISABELLE_LIB=/home/maeder/haskell/Hets-lib/Isabelle/2011
PELLET_PATH=/home/linux-bkb/pellet
HETS_HOL_DIR=/home/linux-bkb/hol-light-20100110/hol_light
HETS_HOLLIGHT_TOOLS=/home/linux-bkb/hets-hollight-tools
HETS_OCAML_LIB_DIR=/home/linux-bkb/ocaml-3.11.2/lib/ocaml/compiler-libs
HETS_MAGIC=/home/linux-bkb/hets-owl-tools/hets.magic

export GHCRTS
export LANG
export TAR
export MAKE
export HETS_OWL_TOOLS
export HETS_ISABELLE_LIB
export PELLET_PATH
export HETS_HOL_DIR
export HETS_HOLLIGHT_TOOLS
export HETS_OCAML_LIB_DIR
export HETS_MAGIC

hetsdir=\
/home/www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets
destdir=$hetsdir/src-distribution/dailyx
outtypes=env,thy,th,dfg,dfg.c,tptp,tptp.c,pp.dol,pp.tex,pp.html,pp.xml,xml,json

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
git clone --depth=50 $HETSBRANCH https://github.com/spechub/Hets
cd Hets
time $MAKE
time $MAKE check
$MAKE release
date
(cd Hets; time $MAKE)
cd ..
}

# within Hets-lib
latexBasicLibraries ()
{
pdflatex Basic-Libraries
}

checkCASLAsHasCASL ()
{
date
for i in Basic/*.casl; do ./hets -v2 -l HasCASL -o th,pp.dol,pp.tex $i; done
latexBasicLibraries
date
for i in Basic/*.pp.dol; do ./hets -v2 -l HasCASL -o pp.dol,pp.tex $i; done
\ls -sh1 Basic/*.pp.*
\rm -f Basic/*.pp.*
}

checkBasicCASL ()
{
date
for i in Basic/*.casl; do ./hets -v2 -o $outtypes $i; done
date
for i in Basic/*.pp.dol; do ./hets -v2 -o pp.dol,pp.tex $i; done
\ls -sh1 Basic/*.pp.*
date
for i in Examples/*.casl CASL/*.casl;  do ./hets -v2 $i; done
}

checkHttpsBasicLib ()
{
date
cd Basic
mkdir -p Basic
for i in *.casl; do ../hets -v2 -o th \
  -L https://svn-agbkb.informatik.uni-bremen.de/Hets-lib/trunk/ \
  Basic/$i; done
cd ..
}

checkUserManual ()
{
date
for i in UserManual/*.casl; do ./hets -v2 -o $outtypes $i; done
}

checkCalculi ()
{
date
for i in Calculi/*/*.casl Calculi/*/*.dol; do ./hets -v2 $i; done
./hets -v4 -n RelationAlgebraSimple -m ConstraintCASL/RCC8.lisp \
  Calculi/Algebra/RelationAlgebraSimple.casl
}

reCheckBasicCASLThs ()
{
date
for i in Basic/*.th; do ./hets -o th,pp.dol $i; done
}

checkHasCASL ()
{
date
for i in HasCASL/*.dol HasCASL/Metatheory/*.dol;
    do ./hets -v2 -o env,th,pp.dol,pp.tex $i; done
if [ -z "$1" ]; then
  pdflatex HasCASL/Metatheory/HasCASL-Metatheory-Libraries.tex
fi
}

checkCspCASL ()
{
date
for i in CspCASL/*.dol CspCASL/Shop/*.dol;
    do ./hets -v2 -o env,th,pp.dol,pp.tex $i; done
pdflatex CspCASL/Shop/Shop.tex
for i in CspCASL/*.{pp.dol,th} CspCASL/Shop/*.{pp.dol,th};
    do ./hets -v2 -o th,pp.dol $i; done
find CspCASL -name \*.th -o -name \*.pp.dol | xargs \rm
}

checkOWL ()
{
date
for i in Ontology/Examples/*.dol;
    do ./hets -v2 -o th,pp.dol,omn $i; done
for i in Ontology/Examples/*.{pp.dol,th};
    do ./hets -v2 -o th,pp.dol $i; done
find Ontology -name \*.th -o -name \*.pp.dol | xargs \rm
}

checkXML ()
{
date
\rm Basic/*.pp.xml
for i in Basic/*.xml;
    do ./hets -v2 -o th,xml $i; done
for i in Basic/*.xml;
    do ./hets -v2 -o th,xml $i; done
for i in Basic/*.casl;
    do ./hets -v2 -A -o xml $i; done
for i in Basic/*.xml;
    do ./hets -v2 -o th,xml $i; done
for i in Basic/*.xml;
    do ./hets -v2 -o th,xml $i; done
for i in Basic/*.xml;
    do ./hets -v2 -o th,xml $i; done
\rm Basic/*.{th,xml}
}

makeLibCheck ()
{
rm -rf Hets-lib
git clone --depth=50 $HETSLIBBRANCH https://github.com/spechub/Hets-lib
cd Hets-lib
mv ../Hets/Hets/hets .
\cp ../Hets/utils/hetcasl.sty .
if [ -z "$1" ]; then
  checkCASLAsHasCASL
fi
checkBasicCASL
checkUserManual
reCheckBasicCASLThs
checkHasCASL $1
checkCspCASL
date
}

checkConservativity ()
{
date
for i in {Basic,UserManual}/*.casl
  do echo globally-check-conservativity | ./hets -I $i
  done > ../cons.log 2>&1
date
}

checkColore ()
{
date
cd CommonLogic
svn co -q --non-interactive --trust-server-cert \
  https://colore.googlecode.com/svn/trunk/ontologies colore
pushd colore
for i in `find . -name \*.clif`; do ../../hets -v2 -C \
  http://colore.oor.net=http://colore.googlecode.com/svn/trunk/ontologies \
  http://colore.oor.net/`echo $i | sed -e 's+\./++g'`; done \
  > ../../../clif.log 2>&1
popd
cd ..
}

checkBioPortal ()
{
cd ..
rm -rf bioportal
git clone --depth=50 git://ontohub.org/bioportal
cd bioportal
for i in `find . -name \*.owl`; do ../Hets-lib/hets -v2 -O . -o xml $i; done \
  > ../bioportal.log 2>&1
cd ../Hets-lib
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
\rm */*.th.pp.dol
\rm */*.pp.pp.dol
cat */*.pp.dol > ../pp.log
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
./hets -v3 -p -i gen_trm -o pp.dol Basic/SimpleDatatypes.tree.gen_trm
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
\cp -fp magic/hets.magic $destdir
}

checkMoreBins ()
{
Haskell/hana ToHaskell/test/*.hascasl.hs
}

makeOWLTools ()
{
$MAKE initialize_java
cp -p OWL2/*.jar $HETS_OWL_TOOLS/
cp -p OWL2/lib/*.jar $HETS_OWL_TOOLS/lib/
cp -p OWL2/lib/native/i686/*.so $HETS_OWL_TOOLS/lib/native/i686
cp -p OWL2/lib/native/x86_64/*.so $HETS_OWL_TOOLS/lib/native/x86_64
cp -p CASL/Termination/AProVE.jar $HETS_OWL_TOOLS/
cp -p magic/hets.magic $HETS_OWL_TOOLS/
}

makeHOLTools ()
{
cp -p HolLight/OcamlTools/exportTools/*.ml $HETS_HOLLIGHT_TOOLS/
}

runIsaHS ()
{
rm -f ../../../../isaHs.log
}

makeCofiLib ()
{
cd /tmp
rm -rf Hets-lib
git clone --depth=50 $HETSLIBBRANCH https://github.com/spechub/Hets-lib
rm -rf Hets-lib/.git
$TAR zcf lib.tgz Hets-lib
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
for i in Basic/*.th; do ./hets -o th,pp.dol $i; done
date
\rm Basic/*.thy
for i in Basic/*.casl;
    do ./hets -v2 -o thy -t CASL2PCFOL:CASL2SubCFOL:CASL2Isabelle $i;
       ./hets -v2 -o dfg.c -t CASL2PCFOL $i; done
date
../Hets/utils/nightly/runisabelle.sh Basic/*.thy > ../isa2.log 2>&1
fgrep \*\*\* ../isa2.log
../Hets/utils/nightly/runSPASS.sh Basic/*.dfg.c > ../spass2.log 2>&1
fgrep "Proof found" ../spass2.log

}

topSortCheck ()
{
cd $HETS_LIB
date
\rm Basic/*.th
\rm Basic/*.thy
for i in Basic/*.casl;
    do ./hets -v2 -o th,thy -t CASL2PCFOLTopSort $i; done
date
for i in Basic/*.th; do ./hets -o th,pp.dol $i; done
date
../Hets/utils/nightly/runisabelle.sh Basic/*.thy > ../isa3.log 2>&1
fgrep \*\*\* ../isa3.log
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

checkHpfs ()
{
date
for i in *.hpf Basic/*.hpf Calculi/*/*.hpf; do ./hets -v2 $i; done
}

updateOMDoc ()
{
svn co -q https://svn-agbkb.informatik.uni-bremen.de/Hets-OMDoc/trunk Hets-OMDoc
cd Hets-OMDoc
make
svn diff
svn ci -m "nightly change"
}

updateLibForCgi ()
{
cd /home/cofi/Hets-lib
svn update -q --ignore-externals
}
