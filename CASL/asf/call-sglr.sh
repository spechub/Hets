#!/bin/sh

TABLE=`dirname $0`/Casl-Lib.trm.tbl

for f in $*
do 
    if [ -f $f ]; then
	sglr -p $TABLE  -A -t -v -l -i $f -o $f.trm 
        mv sglr-stats.txt $f-stats.txt
    fi
done
