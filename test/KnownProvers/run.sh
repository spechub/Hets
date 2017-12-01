#!/bin/bash

# Test if the KnownProversMap works

../../Comorphisms/test/showKP
ret=$?
(exit $ret) && echo "  passed" || echo "  failed"

# Test CMDL_tests
[[ `uname -s` == 'SunOS' ]] && MAKE=gmake || MAKE=make

for i in SoftFOL/tests/CMDL_tests Comorphisms/test/sublogicGraph;
  do (cd ../..; ${MAKE} $i ; $i); done
