#!/usr/local/bin/bash

cvs up -r1.9 GUI/hetdg.hs
cvs up -r1.9 GUI/ConvertDevToAbstractGraph.hs
rm GUI/*.{o,hi}
rm hetdg

make hetdg    # unused imports are reported

rm GUI/Main.hi
rm hetdg

make hetdg   # unused imports are not reported

cvs up -A GUI/*.hs
