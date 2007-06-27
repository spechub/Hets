#!/bin/sh

# Test if the KnownProversMap works

../../Comorphisms/test/showKP
ret=$?
(exit $ret) && echo "  passed" || echo "  failed"

# Test CMDL_tests

../../SoftFOL/tests/CMDL_tests 

# soapTest

../../SoftFOL/tests/soapTest denebola 8080 Broker ProveProblemOpt ../../SoftFOL/tests/asym.tptp 10
