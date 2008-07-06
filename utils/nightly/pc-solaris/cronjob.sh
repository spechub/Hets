#!/bin/bash -x

PATH=/home/pub-bkb/bin:/usr/local/bin:/usr/bin/:/usr/local/X11/bin:/usr/ccs/bin:/home/pkgs/teTeX/3.0/bin/i686-pc-solaris2.10
MAKE=gmake
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

makeHets
cd Hets/Hets
gmake hets.cgi
\cp hets.cgi /home/wwwuser/maeder/cgi-bin/rawhets.cgi
cd ../..

makeLibCheck
createLogFiles
runIsaBasic
runSPASSBasic
installHetsBinary pc-solaris
