#!/bin/sh

# testing Probabilistic Modal Logic formulae
for i in ../probabilistic/*
do 
    echo "~~~~~~processing from $i"
    ../../main 5 $i
done
