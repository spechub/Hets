#!/bin/sh

../../hets -v2 -o thy *.het
../../utils/nightly/runisabelle.sh *.thy

