#!/bin/sh

# testing Probabilistic Modal Logic formulae
for i in ../probabilistic/*
do 
    echo "~~~~~~processing $i"
    ./gnutime -f "Running Time (real): %e" ./timeout 600 ../../main 5 -p $i
done
