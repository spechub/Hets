#!/usr/local/bin/bash

for i in *.hascasl
do
  echo "processing $i"
  ../hetpa $i
  ../hetana $i
done
