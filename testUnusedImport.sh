#!/usr/local/bin/bash

rm GUI/*.{o,hi}
rm hetdg

make hetdg    # unused imports are reported

rm GUI/Main.hi
rm hetdg

make hetdg   # unused imports are not reported

