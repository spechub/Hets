#!/bin/sh

# testing Graded Modal Logic formulae
for i in ../graded/*
do
    echo "~~~~~~processing $i"
    ./gnutime -f "Running Time (real): %e" ./timeout 600 ../../main 4 $i
done
