# $Id$

.PHONY: check

check: hacapa
	./runcheck.sh ../hacapa

output: hacapa 
	./runcheck.sh ../hacapa set

%: 
	(cd ../..; $(MAKE) $@)
