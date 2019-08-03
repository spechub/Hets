#!/bin/sh

../../hets -v2 -o pp.tex *.dol
cp ../../utils/hetcasl.sty .
latex LaTeXDisplayTest.tex

