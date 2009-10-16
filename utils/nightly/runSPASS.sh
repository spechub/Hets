#!/bin/sh

for i in $*
do
  echo $i
  SPASS -TimeLimit=20 -DocProof -PProblem=0 -PGiven=0 $i
done
