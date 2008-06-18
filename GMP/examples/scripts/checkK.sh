#!/bin/sh

# testing K modal logic formulae
for i in ../k_and_kd/*
do
    echo "~~~~~~processing $i"
    ../../main 1 $i
done
