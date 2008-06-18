#!/bin/sh

#testing Coalition Logic formulae
for i in ../coalition/*
do
    echo "~~~~~~processing from $i"
    ../../main 3 $i
done
