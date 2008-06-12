#!/bin/sh

#testing CL formulae
for i in ../cTests/*.cl
do
    echo "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~processing CL f from $i"
    ../../main 3 $i
done
