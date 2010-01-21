#!/bin/sh

CVSROOT=:pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository

isabellescriptspath=../../../utils/nightly

run ()
{
  cd $1
  ../../h2hf $1 *.hs
  $isabellescriptspath/$2.sh *.thy > log 2>&1
  fgrep '***' log
cd ..
}

run HOL runisabelle
\cp -f HOL/*.hs HOLCF/
run HOLCF runHsIsabelle
