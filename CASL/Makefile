# $Id$

.PHONY: check

check: capa 
	bash ./runcheck.sh ./capa

output: capa 
	bash ./runcheck.sh ./capa set

%: 
	(cd ../hetcats; $(MAKE) $@)

