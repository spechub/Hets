#!/bin/sh

# Test if the KnownProversMap works

../../showKP
ret=$?
(exit $ret) && echo "  passed" || echo "  failed"
exit $ret