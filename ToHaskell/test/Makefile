# $Id$

.PHONY: check

check: h2h hacapa
	./runcheck.sh ../h2h

output: h2h hacapa
	./runcheck.sh ../h2h set

%: 
	(cd ../..; $(MAKE) $@)

