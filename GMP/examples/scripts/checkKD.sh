#!/bin/sh

# testing KD modal logic formulae
for i in ../k_and_kd/*
do
    echo "~~~~~~processing from $i"
    ../../main 2 $i
done
