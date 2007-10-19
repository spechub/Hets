#!/bin/sh

HETS_OWL_PARSER=`pwd`/../..
export HETS_OWL_PARSER

rm -f *-local
./replaceLinks.sh

for i in *.owl-local
do
  ../../../hets -i owl $i
done
