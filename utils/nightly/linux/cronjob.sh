#!/bin/bash -x

PATH=/bin:/usr/bin:/usr/X11R6/bin:/home/linux-bkb/bin
UDG_HOME=/home/linux-bkb/uDrawGraph-3.1
MAKE=make
HETS_LIB=/export/local/home/maeder/haskell/Hets-lib

export PATH
export MAKE
export HETS_LIB
export CASL_LIB=$HETS_LIB

hetsdir=/home/www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets
destdir=$hetsdir/src-distribution/daily

cd /local/home/maeder/haskell
. ../cronjob.sh

#makeProgramatica
makeHets
makeLibCheck

# install hets binary
cd Hets-lib
chmod 775 hets
chgrp wwwbkb hets
bzip2 -k hets
\cp -fp hets.bz2 $hetsdir/linux/daily/
chgrp linuxbkb hets
\cp -fp hets /home/linux-bkb/bin/

# copy matching version for hets.cgi
\cp -f ../Hets/utils/hetcasl.sty /home/www.informatik.uni-bremen.de/cofi/hets-tmp/

# make latex documentation
\cp ../Hets/utils/hetcasl.sty .
pdflatex Basic-Libraries

# create some result files
cat */*.th > ../th.log
cat */*.pp.het > ../pp.log

cd Basic
/local/home/maeder/haskell/runisabelle.sh *.thy > ../../isa.log 2>&1
fgrep \*\*\* ../../isa.log
cd ..

/local/home/maeder/haskell/runSPASS.sh Basic/*.dfg > ../spass.log 2>&1

./hets -v2 -o thy Calculi/Time/AllenHayesLadkin_TACAS.het
cd Calculi/Time
/local/home/maeder/haskell/runisabelle.sh *.thy > ../../../isaHC.log 2>&1
fgrep \*\*\* ../../../isaHC.log
cd ../..

./hets -v2 -o thy Calculi/Space/RCCVerification.het
cd Calculi/Space
/local/home/maeder/haskell/runisabelle.sh *.thy > ../../../isaHC2.log 2>&1
fgrep \*\*\* ../../../isaHC2.log
cd ../..

# try out other binaries
../Hets/Syntax/hetpa Basic/LinearAlgebra_II.casl

../Hets/Common/ATerm/ATermLibTest Basic/*.env
diff Basic/LinearAlgebra_II.env Basic/LinearAlgebra_II.env.ttttt

time ../Hets/Common/ATerm/ATermDiffMain Basic/LinearAlgebra_II.env \
    Basic/LinearAlgebra_II.env.ttttt

cats -input=nobin -output=nobin -spec=gen_aterm Basic/SimpleDatatypes.casl
../Hets/ATC/ATCTest Basic/SimpleDatatypes.tree.gen_trm
./hets -v3 -p -i gen_trm -o pp.het Basic/SimpleDatatypes.tree.gen_trm

# build user guide
cd ../Hets/doc
pdflatex UserGuide
bibtex UserGuide
pdflatex UserGuide
pdflatex UserGuide
cd ..

# move docs and release sources to destination
make doc
\cp doc/UserGuide.pdf docs
\cp doc/Programming-Guidelines.txt docs
\cp ../Hets-lib/Basic-Libraries.pdf docs
chgrp -R wwwbkb docs
\cp -rfp docs $destdir
gzip Hets.tar
chmod 664 Hets.tar.gz
chgrp wwwbkb Hets.tar.gz
\cp -fp Hets.tar.gz $destdir

# more tests in Hets
Common/test_parser -p casl_id2 Common/test/MixIds.casl
Haskell/hana ToHaskell/test/*.hascasl.hs
cd Haskell/test/HOLCF
#cp ../HOL/*.hs .
#../../../Haskell/h2hf hc *.hs
#/local/home/maeder/haskell/runHsIsabelle.sh *.thy > ../../../../isaHs.log 2>&1
#fgrep \*\*\* ../../../../isaHs.log

# build and install locally hets.cgi
cd ../../../Hets
#make hets.cgi
#\cp hets.cgi /home/wwwuser/maeder/cgi-bin
cd ..

# pack Hets-lib for cofi at fixed location
cd ../../cofi-libs/
rm -rf Hets-lib
svn co https://svn-agbkb.informatik.uni-bremen.de/Hets-lib/trunk Hets-lib
tar czvf lib.tgz -C Hets-lib --exclude=.svn --exclude=diplom_dw .
chmod 664 lib.tgz
chgrp agcofi lib.tgz
\cp -fp lib.tgz /home/www.informatik.uni-bremen.de/cofi/Libraries/daily/

# repack putting docs into sources on www server
cd $destdir
\rm -rf Hets
tar zxf Hets.tar.gz
\mv docs Hets/docs
\rm -f Hets.tar.gz
tar zcf Hets-src.tgz Hets

# a few more tests
cd $HETS_LIB
date
\rm Basic/*.th
for i in Basic/*.casl;
    do ./hets -v2 -o th -t CASL2SubCFOL $i; done
date
for i in Basic/*.th; do ./hets -v2 -o th,pp.het $i; done
date

date
\rm Basic/*.thy
for i in Basic/*.casl;
    do ./hets -v2 -o thy -t CASL2PCFOL:CASL2SubCFOL:CFOL2IsabelleHOL $i; done
date
/local/home/maeder/haskell/runisabelle.sh Basic/*.thy > ../isa2.log 2>&1
fgrep \*\*\* ../isa2.log

date

#for i in */*.env; \
#   do ./hets -v2 -o prf $i; done
#date
for i in */*.prf; do ./hets -v2 -o th $i; done
date

# check out CASL-lib in /home/cofi/CASL-lib for hets.cgi
cd /home/cofi/Hets-lib
svn update
