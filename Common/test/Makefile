# $Id$

.PHONY: check

check: annos
	bash runcheck.sh ../annos

output: annos
	bash runcheck.sh ../annos set

annos:
	if ! [ -x ../annos ]; then (cd ..; ./ghc-call); fi

%: 
	(cd ../..; $(MAKE) $@)

