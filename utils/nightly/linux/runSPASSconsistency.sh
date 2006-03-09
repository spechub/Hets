#!/bin/sh

for i in $*
do
  echo $i
  SPASS $i | fgrep -C 4 "SPASS beiseite"
done
