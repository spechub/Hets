#!/bin/sh

# testing Monotonic modal logic formulae
for i in ../monotonic/*
do
    echo "~~~~~~processing Monotonic modal logic formula from $i"
    ../../main 1 $i
done
