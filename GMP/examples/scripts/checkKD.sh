#!/bin/sh

# testing KD modal logic formulae
for i in ../k_and_kd/*
do
    echo "~~~~~~processing KD modal logic formula from $i"
    ../../main 2 $i
done
