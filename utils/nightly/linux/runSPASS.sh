#!/bin/sh -x
for i in Basic/*.dfg
do 
  echo $i
  SPASS -Auto=0 $i
done
