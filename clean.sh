#!/bin/sh

# remove files or directories list in "clean.lst"

PATH=/bin/:/usr/bin     # set a safe path

f=`cat clean.lst`

for i in $f 
do 
   rm -rf $i 
done
