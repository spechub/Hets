#!/bin/sh

# Test if the KnownProversMap works

../../Comorphisms/test/showKP
ret=$?
(exit $ret) && echo "  passed" || echo "  failed"

# Test CMDL_tests

../../SPASS/tests/CMDL_tests 

# soapTest

../../SPASS/tests/soapTest denebola 8080 Broker ProveProblemOpt ../../SPASS/tests/asym.tptp 10
