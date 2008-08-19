#!/bin/sh

# testing K modal logic formulae
for i in ../kTests/*.k
do
    echo "~~~processing from $i"
    ./gnutime -f "Running Time (real): %e" ./timeout 5 ../../main 1 $i 
done
