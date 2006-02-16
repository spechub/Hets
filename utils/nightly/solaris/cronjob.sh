#!/bin/bash -x

PATH=/usr/local/bin:/usr/bin/:/usr/local/X11/bin:/home/pub-bkb/bin:/usr/ccs/bin
MAKE=gmake
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/CASL-lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

makeUni
makeProgramatica
makeHets
\cp -f HetCATS/utils/nightly/solaris/cronjob.sh /local/home/maeder/haskell/
makeLibCheck

cd CASL-lib
chmod 775 hets
chgrp wwwbkb hets
bzip2 hets
\cp -fp hets.bz2 \
    /home/www/agbkb/forschung/formal_methods/CoFI/hets/solaris/daily/
