#!/bin/sh

run ()
{
  cd $1
  ../../../ToHaskell/h2hf $1 *.hs
  ./runisabelle.sh >& log
  fgrep '***' log 
  cvs diff -u log
cd ..
}

run HOL
\cp -f HOL/*.hs HOLCF/
run HOLCF


