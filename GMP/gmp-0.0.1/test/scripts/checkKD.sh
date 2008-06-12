#!/bin/sh

# testing KD modal logic formulae
for i in ../kTests/*.k
do
    echo "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~processing KD f from $i"
    ../../main 2 $i
done
