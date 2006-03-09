#!/bin/sh

for i in $*
do
  echo $i
  SPASS -Auto=0 $i
done
