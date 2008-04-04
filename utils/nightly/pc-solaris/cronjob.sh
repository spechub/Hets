#!/bin/bash -x

PATH=/home/maeder/bin:/usr/local/lang/haskell/bin:/usr/local/bin:/usr/bin/:/usr/local/X11/bin:/usr/ccs/bin
MAKE=gmake
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

#makeProgramatica
makeHets
makeLibCheck

cd Hets/Hets
gmake hets.cgi
\cp hets.cgi /home/wwwuser/maeder/cgi-bin/rawhets.cgi
cd ../..

cd Hets-lib
chmod 775 hets
chgrp wwwbkb hets
bzip2 hets
\cp -fp hets.bz2 \
    /home/www/agbkb/forschung/formal_methods/CoFI/hets/pc-solaris/daily/
