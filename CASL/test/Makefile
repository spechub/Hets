# $Id$

.PHONY: check

check: capa 
	./runcheck.sh ../capa

output: capa 
	./runcheck.sh ../capa set

%: 
	(cd ../..; $(MAKE) $@)

