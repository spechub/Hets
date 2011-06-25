#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

for i in tests/*.rdf tests/*.ofn
do
  ../../hets -i ow2 $i
done
