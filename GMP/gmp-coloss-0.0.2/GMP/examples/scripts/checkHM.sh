#!/bin/sh

# testing Hennessy-Milner Logic formulae
for i in ../hennessy_milner/*
do
    echo "~~~~~~processing $i"
    ./gnutime -f "Running Time (real): %e" timeout 600 ../../main 6 -p $i
done
