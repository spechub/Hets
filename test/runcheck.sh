#!/bin/bash

[[ `uname -s` == 'SunOS' ]] && MAKE=gmake || MAKE=make

for i in *
do
  if [ -d "$i" ]; then
    echo "processing $i"
    cd "$i"
    if [ -f Makefile ]
      then ${MAKE}
    elif [ -x run.sh ]
      then ./run.sh
    else echo "nothing done in $i"
    fi
    cd ..
  fi
done

