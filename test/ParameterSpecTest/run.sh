#!/bin/sh

../../hets -v2 -o th -n X_inv ParameterSpecTest.het > log 2>&1
svn diff log
svn diff ParameterSpecTest_X_inv.th
