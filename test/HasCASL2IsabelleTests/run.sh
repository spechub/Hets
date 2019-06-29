#!/bin/sh

../../hets -v2 -o thy *.dol
../../utils/nightly/runisabelle.sh *.thy

