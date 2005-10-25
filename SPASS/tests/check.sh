#!/bin/sh

# SPASS and hets must be in $PATH

cd $HOME/CASL/CASL-lib
export LOG=$PWD/spass_`date "+%a_%b_%e_%H:%M:%S_%Z_%Y"`.log


# cleaning up of old files (snd part is dangerous)
rm -f Basic/*.env Basic/*.dfg

(
# generating dfg files
#for i in Basic/*.casl 
#do 
#    time hets -o dfg $i 
    # rm -f Basic/*.env
#done

time hets -o dfg Basic/*.casl

# checking dfg files with SPASS
for i in Basic/*.dfg 
do 
    echo $i
    time SPASS -Auto=0 $i
done
) > $LOG 2>&1
echo "log is found in "$LOG