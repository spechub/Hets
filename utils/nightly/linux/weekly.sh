#!/bin/bash -x

PATH=/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/bin
HETS_LIB=/local/home/maeder/CASL-lib

export PATH
export HETS_LIB

cd /local/home/maeder
rm -rf CASL-lib
cvs -d \
   :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository \
   co -P CASL-lib
cd CASL-lib

# check differences of *.pp.het and *.pp.pp.het
hets -v2 -o pp.het Basic/*.casl
cat Basic/*.pp.het > pp1.txt
\rm -f Basic/*.env
hets -v2 -o pp.het Basic/*.pp.het
cat Basic/*.pp.pp.het > pp2.txt
diff pp1.txt pp2.txt

# try consistency check with SPASS
hets -v2 -o dfg.c Basic/*.casl
date
/local/home/maeder/haskell/runSPASSconsistency.sh
date

# check other examples
date
for i in */*/*.het */*/*.casl; \
   do hets -v2 -o prf,th,pp.het,pp.tex $i; done
date
for i in */*/*.prf; do hets -v2 -o th $i; done
date
