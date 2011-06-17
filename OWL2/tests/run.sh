#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

#rm -f *-local
#./replaceLinks.sh

for i in *.rdf
do
  ../../hets -i owl $i
done
