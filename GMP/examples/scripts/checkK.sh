#!/bin/sh

# testing K modal logic formulae
for i in ../k_and_kd/*
do
    echo "~~~~~~processing $i"
    ./gnutime -f "Running Time (real): %e" ./timeout 3600 ../../main 1 $i 
done
