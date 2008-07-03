#!/bin/sh

# testing Monotonic modal logic formulae
for i in ../monotonic/*
do
    echo "~~~~~~processing $i"
    ./gnutime -f "Running Time (real): %e" ./timeout 600 ../../main 7 $i
done
