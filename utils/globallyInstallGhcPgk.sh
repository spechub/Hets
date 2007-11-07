#!/bin/bash

prog=$1
installdir=$2

if [ -n "$installdir" ]; then 
$prog configure -p -O --prefix=$installdir
$prog build
$prog haddock
$prog install
else 
echo "usage: $0 setup-prog prefix"
fi  
