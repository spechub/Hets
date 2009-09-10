#!/bin/sh

for i in *.het
do
  ../../hets -v2 -o prf,th,pp.xml -d DGraphXML $i
done

svn diff
