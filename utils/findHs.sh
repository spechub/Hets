#!/bin/bash

os=`find . -name \*.hs`

for i in $os
do
    if [ ! -e `dirname $i`/`basename $i .hs`.o ]
    then
      echo $i
    fi
done
