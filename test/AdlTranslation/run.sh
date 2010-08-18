#!/bin/sh

../../hets -v2 -o pp.het,pp.tex,th,dfg.c -t Adl2CASL -l Adl *.adl
../../hets -v2 -o pp.het -l Adl *.het
ls -l *.pp.het
../../hets -v2 -o pp.het *.th
for i in *.dfg.c
do
  SPASS $i
done
