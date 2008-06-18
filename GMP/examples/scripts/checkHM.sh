#!/bin/sh

# testing Hennessy-Milner Logic formulae
for i in ../hennessy_milner/*
do
    echo "~~~~~~processing Hennessy Milner Logic formula from $i"
    ../../main 6 $i 
done
