# $Id$

.PHONY: check

check: annos
	./runcheck.sh ../annos

output: annos
	./runcheck.sh ../annos set

annos:
	if test ! -x ../annos; then (cd ..; ./ghc-call); fi

%: 
	(cd ../..; $(MAKE) $@)

