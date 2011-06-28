#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS


for i in *.rdf
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
done

for i in *.rdf
do
  ../../hets -v2 -i ow2 -o th $i
done

for i in *.het
do
  ../../hets -l OWL -v2 -o th $i
done

for i in *.th
do
  ../../hets -v2 $i
done

