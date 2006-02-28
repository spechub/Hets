#!/bin/bash -x

PATH=/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/bin
HETS_LIB=/local/home/maeder/haskell/CASL-lib

export PATH
export HETS_LIB

cd $HETS_LIB

# check differences of *.pp.het and *.pp.pp.het
mkdir pp1
cp Basic/*.pp.het pp1/
\rm -f Basic/*.env
./hets -v2 -o pp.het Basic/*.pp.het
mkdir pp2
mv Basic/*.pp.pp.het pp2/
diff pp1 pp2
\rm -rf pp1 pp2

# check other examples
date
for i in */*/*.het */*/*.casl; \
   do ./hets -v2 -o prf,th,pp.het,pp.tex $i; done
date
for i in */*/*.prf; do ./hets -v2 -o th $i; done
date

# try consistency check with SPASS
./hets -v2 -o dfg.c Basic/*.casl
date
/local/home/maeder/haskell/runSPASSconsistency.sh > /dev/null
date

# install a newer binary 
#chgrp linuxbkb hets
#\cp -fp hets /home/linux-bkb/bin/
