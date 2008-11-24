#!/bin/sh

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

rm -f *-local
./replaceLinks.sh

for i in *-local
do
  ../../hets -v2 -i owl -o th,owl $i
done
