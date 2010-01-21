#!/bin/sh

for i in $*
do
   j=`basename $i .thy`
   ( cd `dirname $i`; \
     echo " use_thy \"$j\"; quit;" \
     | isabelle tty -l HOLCF )
done
