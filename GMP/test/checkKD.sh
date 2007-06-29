#!/bin/sh

# testing KD modal logic formulae
for i in *.kd
do
    echo "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~processing KD f from $i"
    ../main 2 $i
done
