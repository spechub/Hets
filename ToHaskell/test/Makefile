# $Id$

.PHONY: check

check: translateAna
	./runcheck.sh ../translateAna

output: translateAna
	./runcheck.sh ../translateAna set

translateAna:
	if test ! -x ../translateAna; then (cd ..; ./ghc-call); fi

%: 
	(cd ../..; $(MAKE) $@)

