#!/bin/sh

#testing CL formulae
for i in *.cl
do
    echo "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~processing CL f from $i"
    ../main 3 $i
done
