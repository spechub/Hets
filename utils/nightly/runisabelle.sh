#!/bin/sh

for i in $*
do
   j=`basename $i .thy`
   ( cd `dirname $i`; \
     isabelle-process -q -e  \
       " use_thy \"$j\"; \
         theory \"$j\"; \
         quit(); " )
done
