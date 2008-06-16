#!/bin/sh

# testing K modal logic formulae
for i in ../k_and_kd/*
do
    echo "~~~~~~processing K modal logic formula from $i"
    ../../main 1 $i
done
