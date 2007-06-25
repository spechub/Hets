#!/bin/bash -x

PATH=/local/home/maeder/bin:/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/bin
HETS_LIB=/local/home/maeder/monthly/Hets-lib

export PATH
export HETS_LIB

cd $HETS_LIB

# try consistency check with SPASS
hets -v2 -o dfg.c Basic/*.casl UserManual/*.casl
date
$HETS_LIB/runSPASSconsistency.sh */*.dfg.c
date
