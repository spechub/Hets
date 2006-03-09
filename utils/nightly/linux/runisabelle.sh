#!/bin/sh

for i in $*
do
   j=`basename $i .thy`
   isabelle -q -e "use_thy \"$j\";print_depth 300;theory \"$j\";axioms_of it;quit();"
done
