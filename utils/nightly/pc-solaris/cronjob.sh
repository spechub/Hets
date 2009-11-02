#!/bin/bash -x

PATH=/home/pub-bkb/bin:/usr/bin/:/usr/ccs/bin:/opt/csw/bin:/opt/csw/gcc4/bin
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib
LD_LIBRARY_PATH=/home/wwwuser/maeder/cgi-bin

export PATH
export UDG_HOME
export HETS_LIB
export LD_LIBRARY_PATH

cd /local/home/maeder/haskell

. ../cronjob.sh

makeHets
cd Hets/Hets
gmake hets.cgi
\cp hets.cgi /home/wwwuser/maeder/cgi-bin/rawhets.cgi
cd ../..

makeLibCheck
installHetsBinary pc-solaris
\cp -fp hets /home/pub-bkb/pc-solaris/bin/

copyStyForCgi
latexBasicLibraries
createLogFiles

checkConsOf Calculi/Space/Interval.casl Inter
checkConsOf Calculi/Space/OrientationCalculi.het Ori
checkConsOf Calculi/Algebra/FuzzySystems.het Fuzzy

runIsaBasic
runSPASSBasic
runDarwinBasic

makeSources
makeCofiLib
repackDocs
updateLibForCgi

moreChecks
checkCalculi
checkEnvs
checkHpfs
ssh denebola "(cd /tmp; \rm -f eprover* formalDescription* tstp* *.tptp)"
