#!/bin/sh -x
for i in Basic/*.dfg.c
do 
  echo $i
  SPASS $i
done
