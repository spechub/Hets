#!/bin/sh

../../hets -v2 -A -o thy *.dol
../../utils/nightly/runisabelle.sh *.thy

../../hets -l HasCASL -v2 -A -o thy *.dol
../../utils/nightly/runisabelle.sh *.thy
