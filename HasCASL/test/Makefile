# $Id$

.PHONY: check

check: hacapa
	./runcheck.sh ../hacapa

output: 
	./runcheck.sh ../hacapa set

%: 
	(cd ../..; $(MAKE) $@)
