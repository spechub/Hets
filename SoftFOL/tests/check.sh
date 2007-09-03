#!/bin/bash

# SPASS and hets must be in $PATH

cd $1
export LOG=$PWD/spass_`date "+%a_%b_%d_%H:%M:%S_%Z_%Y"`.log


# cleaning up of old files (snd part is dangerous)
rm -f Basic/*.env Basic/*.dfg

(time(
# generating dfg files

hets -o dfg Basic/*.casl

# checking dfg files with SPASS
for i in Basic/*.dfg
do
    echo $i
    SPASS -Auto=0 $i
done
)) > $LOG 2>&1
echo "log is found in "$LOG
