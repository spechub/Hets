#!/bin/bash -x

PATH=/home/pub-bkb/bin:/bin:/usr/bin:/usr/local/bin/:/usr/X11R6/bin:/opt/local/bin:/sw/bin
MAKE=make
UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
HETS_LIB=/local/home/maeder/haskell/Hets-lib

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /local/home/maeder/haskell

. ../cronjob.sh

makeHets
makeLibCheck

installHetsBinary mac
