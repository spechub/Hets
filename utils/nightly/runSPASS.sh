#!/bin/sh

for i in $*
do
  echo $i
  SPASS -DocProof -PProblem=0 -PGiven=0 $i
done
