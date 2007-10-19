#!/bin/sh

HETS_OWL_PARSER=`pwd`/../..
export HETS_OWL_PARSER

for i in *.owl-local *.xml-local
do
  ../../../hets -i owl $i
done
