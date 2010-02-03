#!/bin/bash -x

PATH=/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/Isabelle/Isabelle2009/bin:/home/linux-bkb/bin
UDG_HOME=/home/linux-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export HETS_LIB
export CASL_LIB=$HETS_LIB

cd /tmp
\rm -f eprover* formalDescription* tstp*
cd /local/home/maeder/haskell
. ../cronjob.sh

ssh bigmac launchctl load /home/maeder/Library/LaunchAgents/makeHets.plist
ssh m18 /Users/Shared/maeder/haskell/job.sh &

makeHets

ssh bigmac date

makeLibCheck
installHetsBinary linux
chgrp linuxbkb hets
\cp -fp hets /home/linux-bkb/hets/hets-latest/bin/

copyStyForCgi
latexBasicLibraries
createLogFiles

runIsaBasic
runSPASSBasic
checkIsaOf Calculi/Time/AllenHayesLadkin_TACAS.het HC
checkIsaOf Calculi/Space/RCCVerification.het HC2

checkBins
checkCats
makeSources

checkMoreBins
makeOWLTools
runIsaHS

makeCofiLib
repackDocs

moreChecks
checkEnvs
checkPrfs
date
updateOMDoc
