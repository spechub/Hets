#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

for i in *.rdf
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
done

for i in *.rdf
do
  ../../hets -v2 -i ow2 -o th,pp.het,omn $i
done

for i in OWL2tests/*.ofn *.rdf
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
  ../../hets -v2 -i ow2 -o th,pp.het,omn $i
done

for i in *.het
do
  ../../hets -l OWL -v2 -o th,pp.het,omn $i
done

for i in *.th *.pp.het *.omn
do
  ../../hets -l OWL -v2 $i
done

rm -f *.pp.het *.th *.omn OWL2tests/*.pp.het OWL2tests/*.th OWL2tests/*.omn
