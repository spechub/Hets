#!/bin/sh

for i in *.het
do
  ../../hets -v2 -A --relative-positions -o th,pp.xml,xml $i
done

git --no-pager diff ParameterSpecTest_X_inv.th ParamView.pp.xml ParamView.xml
