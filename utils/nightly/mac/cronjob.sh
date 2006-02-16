#!/bin/bash -x

PATH=/home/mac-bkb/bin:/bin:/usr/bin:/usr/local/bin/:/usr/X11R6/bin
MAKE=make
UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/CASL-lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

# cd uni
# cvs up -dPA
# make packages
# cd ..

# cd programatica/tools/base
# cvs up -dPA
# cd ../../..
# cd programatica/tools/property
# cvs up -dPA
# cd ../../..

makeHets
makeLibCheck

cd CASL-lib
chmod 775 hets
chgrp wwwbkb hets
bzip2 hets
\cp -fp hets.bz2 /home/www/agbkb/forschung/formal_methods/CoFI/hets/mac/daily/

