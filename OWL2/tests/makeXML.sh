#!/bin/sh

for i in *.rdf
do
    java -jar ../OWL2Parser.jar file://`pwd`/$i xml >> `pwd`/XML/$i.xml
done

cd ../..

make OWL2/runConv

for i in OWL2/tests/XML/*.xml
do
    OWL2/runConv $i >> $i.xml2
done
