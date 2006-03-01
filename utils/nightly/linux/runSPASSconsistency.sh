#!/bin/bash

for i in Basic/*.dfg.c
do 
  echo $i
  SPASS $i | fgrep -C 4 "SPASS beiseite"
done
