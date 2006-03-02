#!/bin/bash -x

PATH=/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/bin
UDG_HOME=/home/linux-bkb/uDrawGraph-3.1
MAKE=make
HETS_LIB=/local/home/maeder/haskell/CASL-lib
GHCRTS='-H300m -M1g'

export PATH 
export MAKE
export HETS_LIB
export GHCRTS

hetsdir=/home/www/agbkb/forschung/formal_methods/CoFI/hets
hetsbin=$hetsdir/linux/daily/hets
destdir=$hetsdir/src-distribution/daily

cd /local/home/maeder/haskell
. ../cronjob.sh

# set BDBDIR for a full uni installation
# makeUni
# makeProgramatica
makeHets
# copy cronjob scripts for the next night
\cp -f HetCATS/utils/nightly/cronjob.sh /home/maeder/haskell/
\cp -f HetCATS/utils/nightly/linux/*.sh /local/home/maeder/haskell/
makeLibCheck

cd CASL-lib
chmod 775 hets
chgrp wwwbkb hets
\cp -fp hets $hetsbin
\rm -f $hetsbin.bz2
bzip2 $hetsbin

\cp ../HetCATS/utils/hetcasl.sty .
pdflatex Basic-Libraries

cat */*.th > ../th.log
cat */*.pp.het > ../pp.log

cd Basic
/local/home/maeder/haskell/runisabelle.sh > ../../isa.log 2>&1
fgrep \*\*\* ../../isa.log
cd ..

/local/home/maeder/haskell/runSPASS.sh > ../spass.log 2>&1

./hets -v2 -o thy Calculi/Time/AllenHayesLadkin_TACAS.het
cd Calculi/Time
/local/home/maeder/haskell/runisabelle.sh > ../../../isaHC.log 2>&1
fgrep \*\*\* ../../../isaHC.log
cd ../..

./hets -v2 -o thy Calculi/Space/RCCDagstuhl2.het
cd Calculi/Space
/local/home/maeder/haskell/runisabelle.sh > ../../../isaHC2.log 2>&1
fgrep \*\*\* ../../../isaHC2.log
cd ../..


../HetCATS/hetpa Basic/LinearAlgebra_II.casl
../HetCATS/hetana Basic/LinearAlgebra_II.casl

../HetCATS/atermlibtest Basic/*.env
diff Basic/LinearAlgebra_II.env Basic/LinearAlgebra_II.env.ttttt

time ../HetCATS/hatermdiff Basic/LinearAlgebra_II.env \
    Basic/LinearAlgebra_II.env.ttttt

cats -input=nobin -output=nobin -spec=gen_aterm Basic/SimpleDatatypes.casl
../HetCATS/atctest Basic/SimpleDatatypes.tree.gen_trm
./hets -v3 -p -i gen_trm -o pp.het Basic/SimpleDatatypes.tree.gen_trm

cd ../HetCATS/doc
latex UserGuide
bibtex UserGuide
latex UserGuide
latex UserGuide
dvips UserGuide.dvi -o UserGuide.ps
cd ..

make doc
\cp doc/UserGuide.ps docs
\cp doc/Programming-Guidelines.txt docs
\cp ../CASL-lib/Basic-Libraries.pdf docs
chgrp -R wwwbkb docs
\cp -rfp docs $destdir
gzip HetCATS.tar
chmod 664 HetCATS.tar.gz
chgrp wwwbkb HetCATS.tar.gz
\cp -fp HetCATS.tar.gz $destdir

Common/test_parser -p casl_id2 Common/test/MixIds.casl
Haskell/hana ToHaskell/test/*.hascasl.hs
cd Haskell/test/HOLCF
cp ../HOL/*.hs .
../../../ToHaskell/h2hf hc *.hs
/local/home/maeder/haskell/runHsIsabelle.sh > ../../../../isaHs.log 2>&1
fgrep \*\*\* ../../../../isaHs.log

cd ../../../HetCATS
make hets.cgi
\cp hets.cgi /home/www/users/maeder/cgi-bin
cd ..

cd ../..
cd CASL-lib
cvs up -dPA
cd ..
tar czvf lib.tgz -C CASL-lib --exclude=CVS --exclude=.cvsignore \
    --exclude=diplom_dw .
chmod 664 lib.tgz
chgrp agcofi lib.tgz
\cp -fp lib.tgz /home/www/cofi/Libraries/daily/

cd $destdir
\rm -rf HetCATS
tar zxf HetCATS.tar.gz
\mv docs HetCATS/docs
\rm -f HetCATS.tar.gz
tar zcf Hets-src.tgz HetCATS

cd $HETS_LIB
date
for i in */*.env; \
   do ./hets -v2 -o prf $i; done
date
for i in */*.prf; do ./hets -v2 -o th $i; done
date
