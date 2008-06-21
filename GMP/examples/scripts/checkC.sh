#!/bin/sh

#testing Coalition Logic formulae
for i in ../coalition/*
do
    echo "~~~~~~processing $i"
    ./gnutime -f "Running Time (real): %e" timeout 600 ../../main 3 $i
done
