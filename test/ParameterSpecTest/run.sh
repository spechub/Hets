#!/bin/sh

../../hets -v2 -o th -n X_inv ParameterSpecTest.het > log 2>&1
cvs diff log
cvs diff ParameterSpecTest_X_inv.th
