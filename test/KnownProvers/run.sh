#!/bin/sh

# Test if the KnownProversMap works

../../Comorphisms/test/showKP
ret=$?
(exit $ret) && echo "  passed" || echo "  failed"

# Test CMDL_tests

for i in Comorphisms/test/sublogicGraph;
  do (cd ../..; make $i ; $i); done
