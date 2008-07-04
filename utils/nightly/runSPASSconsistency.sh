#!/bin/sh

for i in $*
do
  echo $i
  time SPASS $i | egrep -B 1 -A 6 -f spass_consistency_patterns.txt
  mv $i $i.fin
done
