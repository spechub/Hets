# $Id$

.PHONY: check

check: hatch
	./runcheck.sh ../hatch

output: hatch
	./runcheck.sh ../hatch set

hatch:
	if test ! -x ../hatch; then (cd ..; ./ghc-call); fi

%: 
	(cd ../../..; $(MAKE) $@)

