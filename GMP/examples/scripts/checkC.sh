#!/bin/sh

#testing Coalition Logic formulae
for i in ../coalition/*
do
    echo "~~~~~~processing Coalition formula from $i"
    ../../main 3 $i
done
