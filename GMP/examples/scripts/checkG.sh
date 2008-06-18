#!/bin/sh

# testing Graded Modal Logic formulae
for i in ../graded/*
do
    echo "~~~~~~processing from $i"
    ../../main 4 $i 
done
