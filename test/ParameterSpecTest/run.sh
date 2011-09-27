#!/bin/sh

for i in *.het
do
  ../../hets -v2 -A --relative-positions -o th,pp.xml,xml $i
done

svn diff
