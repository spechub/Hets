#!/bin/sh

../../hets -v2 -o thy *.het
../../utils/nightly/linux/runisabelle.sh *.thy

