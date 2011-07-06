#!/bin/bash

if [ -z $1 ]
then
  path=.
else
  path=$1
fi

os=`find $path -name \*.hs -a ! -name \*.der.hs -a ! -name \*.inline.hs`

for i in $os
do
    if [ ! -e `dirname $i`/`basename $i .hs`.o ]
    then
      echo $i
    fi
done
