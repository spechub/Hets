#!/bin/sh

# testing Probabilistic Modal Logic formulae
for i in ../probabilistic/*
do 
    echo "~~~~~~processing probabilistic logic formula from $i"
    ../../main 5 $i
done
