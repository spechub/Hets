#!/bin/sh

for i in */ 
do
  echo "processing $i"
  cd $i
  if [ -f Makefile ] 
      then gmake
  elif [ -x run.sh ] 
      then ./run.sh
  else echo "nothing done in $i" 
  fi 
  cd ..
done
  
