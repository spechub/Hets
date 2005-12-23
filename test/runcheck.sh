#!/bin/sh

CVSROOT=:pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository

export CVSROOT

for i in *
do
  if [ -d $i ]; then
    echo "processing $i"
    cd $i
    if [ -f Makefile ] 
      then gmake
    elif [ -x run.sh ] 
      then ./run.sh
    else echo "nothing done in $i" 
    fi 
    cd ..
  fi 
done
  
