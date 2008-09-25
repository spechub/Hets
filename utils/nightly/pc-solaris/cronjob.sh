#!/bin/bash -x

PATH=/home/pub-bkb/bin:/usr/local/bin:/usr/bin/:/usr/local/X11/bin:/usr/ccs/bin:/home/pkgs/teTeX/3.0/bin/i686-pc-solaris2.10
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export UDG_HOME
export HETS_LIB

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
