#!/bin/sh

../../hets -v2 -o pp.dol,pp.tex,th,dfg.c -t Adl2CASL -l Adl *.adl
../../hets -v2 -o pp.dol -l Adl *.dol
ls -l *.pp.dol
../../hets -v2 -o pp.dol *.th
for i in *.dfg.c
do
  SPASS $i
done
