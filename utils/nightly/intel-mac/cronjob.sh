#!/bin/bash -x

PATH=/home/pub-bkb/bin:/usr/local/bin:/bin:/usr/bin:/usr/X11R6/bin:/opt/local/bin:/sw/bin
MAKE=make
UDG_HOME=/home/mac-bkb/uDrawGraph-3.1
HETS_LIB=/Users/Shared/maeder/haskell/Hets-lib
export MACOSX_DEPLOYMENT_TARGET=10.4

export PATH
export MAKE
export UDG_HOME
export HETS_LIB

cd /Users/Shared/maeder/haskell

. ../cronjob.sh

makeHets
makeLibCheck

installHetsBinary intel-mac
