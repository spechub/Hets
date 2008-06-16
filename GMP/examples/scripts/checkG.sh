#!/bin/sh

# testing Graded Modal Logic formulae
for i in ../graded/*
do
    echo "~~~~~~processing Graded Modal Logic formula from $i"
    ../../main 4 $i 
done
