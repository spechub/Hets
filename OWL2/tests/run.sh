#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

for i in *.rdf
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
done

for i in *.rdf
do
  ../../hets -v2 -i owl -o th,pp.dol,omn $i
done

for i in *.rdf *.omn
do
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omnm
  ../../hets -v2 -i owl -o th,pp.dol,omn $i
done

for i in *.dol
do
  ../../hets -l OWL -v2 -o th,pp.dol,omn $i
done

for i in *.th *.pp.dol *.omn
do
  ../../hets -l OWL -v2 $i
done

for i in *.omn
do
  echo $i
  java -jar ../OWL2Parser.jar file://`pwd`/$i $i.omn2
done

#rm -f *.pp.dol *.th *.omn *.omn2
