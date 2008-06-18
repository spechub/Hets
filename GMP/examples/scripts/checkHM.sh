#!/bin/sh

# testing Hennessy-Milner Logic formulae
for i in ../hennessy_milner/*
do
    echo "~~~~~~processing from $i"
    ../../main 6 $i 
done
