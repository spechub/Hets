#!/bin/bash -x

PATH=/home/pub-bkb/bin:/home/pub-bkb/pc-solaris/bin:/usr/bin:/opt/csw/bin:/usr/ccs/bin
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

makeHets
cd Hets/Hets
gmake o_clean
gmake hets.cgi
gmake hets.cgi
\cp hets.cgi /home/wwwuser/maeder/cgi-bin/hets.cgi
cd ../..

makeLibCheck
installHetsBinary pc-solaris
\cp -fp hets /home/pub-bkb/pc-solaris/hets/bin/

copyStyForCgi
latexBasicLibraries
createLogFiles

checkConsOf Calculi/Space/Interval.casl Inter
checkConsOf Calculi/Space/OrientationCalculi.dol Ori
checkConsOf Calculi/Algebra/FuzzySystems.dol Fuzzy

runIsaBasic
runSPASSBasic
runDarwinBasic

makeSources
makeCofiLib
repackDocs
updateLibForCgi

topSortCheck
checkXML
#moreChecks
checkCalculi
checkEnvs
checkHpfs
ssh denebola "(cd /tmp; \rm -f eprover* formalDescription* tstp* *.tptp)"
