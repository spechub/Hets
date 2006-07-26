#!/bin/sh

# Test if the KnownProversMap works

../../Comorphisms/test/showKP
ret=$?
(exit $ret) && echo "  passed" || echo "  failed"
exit $ret
