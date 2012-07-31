#!/bin/bash -x

PATH=/local/home/maeder/ghc/bin:/local/home/maeder/gcc/bin:/home/pub-bkb/bin:/opt/csw/bin:/usr/bin/:/usr/ccs/bin
UDG_HOME=/home/pub-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

makeHets
makeLibCheck faster

installHetsBinary solaris
