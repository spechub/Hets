#!/bin/bash

for i in *.rdf *.nt
do
    hets -i rdf $i -o th,pp.dol
done

for i in *.pp.dol *.th
do
    hets -l RDF $i -o th,pp.dol
done

for i in *pp* *th*
do
    hets -l RDF $i
done

rm *th* *pp*
