#!/bin/sh

# testing String-indexed formulae
for i in ../sTests/*.s
do
    echo "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~processing Generic f from $i"
    ../../main 0 $i
done
