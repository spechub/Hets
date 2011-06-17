#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

for i in *.rdf
do
  ../../hets -i owl $i
done
