# $Id$

.PHONY: check

check: h2h hacapa
	./runcheck.sh ../../Haskell/h2h

output: h2h hacapa
	./runcheck.sh ../../Haskell/h2h set

%: 
	(cd ../..; $(MAKE) $@)

