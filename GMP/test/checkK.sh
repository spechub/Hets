#!/bin/sh

# testing String-indexed formulae
for i in *.s
do
    echo "~~~processing Generic f from $i"
    ../main 0 $i
done
# testing K modal logic formulae
for i in *.k
do
    echo "~~~processing K f from $i" 
    ../main 1 $i
done
# testing KD modal logic formulae
for i in *.kd
do
    echo "~~~processing KD f from $i"
    ../main 2 $i
done
#testing CL formulae
for i in *.cl
do
    echo "~~~processing CL f from $i"
    ../main 3 $i
done
# testing GML formulae
for i in *.g
do
    echo "~~~processing GML f from $i"
    ../main 4 $i
done
