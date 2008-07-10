#!/bin/bash -x

export PATH=/home/pub-bkb/bin:/usr/local/bin:/bin:/usr/bin:/usr/X11R6/bin:/opt/local/bin:/sw/bin
export UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
export HETS_LIB=/Users/Shared/maeder/haskell/Hets-lib
export MACOSX_DEPLOYMENT_TARGET=10.4 #this is not enough

cd /Users/Shared/maeder/haskell

. ../cronjob.sh

makeHets
makeLibCheck

installHetsBinary intel-mac
chgrp macbkb hets
\cp -fp hets /home/mac-bkb/intel/bin/

createLogFiles
runIsaBasic
runSPASSBasic
runDarwinBasic

checkEnvs
checkPrfs
