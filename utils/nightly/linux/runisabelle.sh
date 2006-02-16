#!/bin/sh --login

PATH=$PATH:/home/linux-bkb/bin

cd /local/home/maeder/haskell/CASL-lib/Basic

for i in *.thy
do
   j=`basename $i .thy`
   isabelle -q -e "use_thy \"$j\";print_depth 300;theory \"$j\";axioms_of it;quit();"
done
