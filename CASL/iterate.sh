#!/usr/local/bin/bash

for i in *.{casl,output,hs};
do
    cvs diff $i
done