#!/bin/sh
TESTDIR="$(dirname $0)"
cd $TESTDIR
( cd ../.. && make )

echo "Testing UML languages"

set -e  # propagate failures
../../hets atm-mod.het

echo "TODO: This should output the normalised System and reparse once I find out how to do that on the command line."
