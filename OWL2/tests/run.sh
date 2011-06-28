#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

for i in RDF/*.rdf
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
done

for i in RDF/*.rdf
do
  ../../hets -v2 -i ow2 -o th,pp.het,omn $i
done

for i in RDF/*.rdf OMN/*.omn
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
  ../../hets -v2 -i ow2 -o th,pp.het,omn $i
done

for i in HET/*.het
do
  ../../hets -l OWL -v2 -o th,pp.het,omn $i
done

for i in *.th *.pp.het *.omn
do
  ../../hets -l OWL -v2 $i
done

for i in OMN/*.omn
do
  echo $i
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omn2
done

#rm -f *.pp.het *.th *.omn *.omn2
