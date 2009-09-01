#!/bin/bash -x

export PATH=/home/pub-bkb/bin:/bin:/usr/bin:/usr/local/bin/:/usr/X11R6/bin:/opt/local/bin:/sw/bin
export UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
export HETS_LIB=/Users/Shared/maeder/haskell/Hets-lib

cd /Users/Shared/maeder/haskell

. ../cronjob.sh

makeHets
makeLibCheck

strip hets
installHetsBinary mac
chgrp macbkb hets
\cp -fp hets /home/mac-bkb/hets/hets-latest/bin/
