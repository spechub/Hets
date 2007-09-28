#!/bin/sh

for i in *.owl *.xml
do
  java -jar ../OWLParser.jar file://`pwd`/$i
done
