#!/bin/sh

# testing ML formulae
for i in *.m
do 
    echo "~~~"
    ../main 5 $i
done
