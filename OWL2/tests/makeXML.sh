#!/bin/sh

for i in *.rdf pizza.owl
do
    java -jar ../OWL2Parser.jar file:`pwd`/$i xml >> `pwd`/XML/$i.xml
done

cd ../..

make OWL2/scripts/runConv

for i in OWL2/tests/XML/*.xml
do
    OWL2/scripts/runConv $i >> $i.xml
done

for i in OWL2/tests/XML/*.xml.xml
do
    OWL2/scripts/runConv $i >> $i.xml
done

cd OWL2/tests/XML

for i in *.rdf.xml.xml
do
    diff $i $i.xml
done


