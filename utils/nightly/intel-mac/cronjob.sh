#!/bin/bash -x

PATH=/home/mac-bkb/bin:/usr/local/bin:/bin:/usr/bin:/usr/X11R6/bin:/sw/bin:/home/mac-bkb/intel/bin:/opt/local/bin
MAKE=make
UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
HETS_LIB=/Users/Shared/maeder/haskell/Hets-lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /Users/Shared/maeder/haskell

. ../cronjob.sh

#makeProgramatica
makeHets
makeLibCheck

cd Hets-lib
chmod 775 hets
chgrp wwwbkb hets
bzip2 hets
\cp -fp hets.bz2 /home/www/agbkb/forschung/formal_methods/CoFI/hets/intel-mac/daily/
