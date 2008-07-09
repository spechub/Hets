#!/bin/bash -x

export PATH=/home/pub-bkb/bin:/bin:/usr/bin:/usr/local/bin/:/usr/X11R6/bin:/opt/local/bin:/sw/bin
export UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
export HETS_LIB=/local/home/maeder/haskell/Hets-lib

cd /local/home/maeder/haskell

. ../cronjob.sh

makeHets
makeLibCheck

installHetsBinary mac
chgrp macbkb hets
\cp -fp hets /home/mac-bkb/bin/
