#!/bin/sh

for i in $*
do
   j=`basename $i .thy`
   echo $j
   ( cd `dirname $i`; \
     echo " use_thy \"$j\"; quit;" \
     | isabelle-process )
done
