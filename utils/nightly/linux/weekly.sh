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

# check differences of *.pp.dol and *.pp.pp.dol
hets -v2 -o pp.dol Basic/*.casl
cat Basic/*.pp.dol > pp1.txt
\rm -f Basic/*.env
hets -v2 -o pp.dol Basic/*.pp.dol
cat Basic/*.pp.pp.dol > pp2.txt
diff pp1.txt pp2.txt

# try consistency check with SPASS
hets -v2 -o dfg.c Basic/*.casl UserManual/*.casl
date
cp /local/home/maeder/haskell/spass_consistency_patterns.txt .
/local/home/maeder/haskell/runSPASSconsistency.sh */*.dfg.c
date

# check other examples
date
for i in */*/*.dol */*/*.casl; \
   do hets -v2 -o prf,th,pp.dol,pp.tex $i; done
date
for i in */*/*.prf; do hets -v2 -o th $i; done
date
