#!/bin/sh

for i in $*
do
   j=`basename $i .thy`
   (cd `dirname $i`; isabelle -q -e "use_thy \"$j\";print_depth 300;theory \"$j\";axioms_of it;quit();")
done
