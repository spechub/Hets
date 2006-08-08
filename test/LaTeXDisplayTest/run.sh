#!/bin/sh

../../hets -v2 -o pp.tex *.het
cp ../../utils/hetcasl.sty .
latex LaTeXDisplayTest.tex

