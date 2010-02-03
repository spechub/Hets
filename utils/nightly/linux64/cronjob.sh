#!/bin/bash -x

PATH=/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/Isabelle/Isabelle2009/bin:/home/linux-bkb/bin
UDG_HOME=/home/linux-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export HETS_LIB

cd /local/home/maeder/haskell
. ../cronjob.sh

export GHCRTS='-H300m -M6g'

makeHets
makeLibCheck
installHetsBinary linux64
chgrp linuxbkb hets
\cp -fp hets /home/linux64-bkb/hets/hets-latest/bin/

latexBasicLibraries
createLogFiles

runIsaBasic
runSPASSBasic
checkIsaOf Calculi/Time/AllenHayesLadkin_TACAS.het HC
checkIsaOf Calculi/Space/RCCVerification.het HC2

checkBins

cd ../Hets
checkMoreBins
runIsaHS

moreChecks
checkEnvs
checkPrfs
#checkHpfs
date
updateOMDoc
date
