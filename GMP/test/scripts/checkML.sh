#!/bin/sh

# testing ML formulae
for i in ../mTests/*.m
do 
    echo "~~~"
    ../../main 5 $i
done
