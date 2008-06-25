#!/bin/bash -x

PATH=/home/maeder/haskell/solaris/bin:/home/pub-bkb/bin:/usr/local/bin:/usr/bin/:/usr/local/X11/bin:/usr/ccs/bin
MAKE=gmake
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/home/maeder/haskell/V240-solaris/haskell/Hets-lib
LD_LIBRARY_PATH=/home/maeder/haskell/solaris/lib:/usr/local/lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB
export LD_LIBRARY_PATH

cd /home/maeder/haskell/V240-solaris/haskell

. ../cronjob.sh

makeHets
makeLibCheck

cd Hets-lib
chmod 775 hets
chgrp wwwbkb hets
bzip2 hets
\cp -fp hets.bz2 \
    /home/www/agbkb/forschung/formal_methods/CoFI/hets/solaris/daily/
