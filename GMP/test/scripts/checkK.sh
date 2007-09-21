#!/bin/sh

# testing K modal logic formulae
for i in ../kTests/*.k
do
    echo "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~processing K f from $i"
    ../../main 1 $i
done
