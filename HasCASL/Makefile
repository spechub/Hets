# $Id$

.PHONY: check

check: hacapa 
	bash ./runcheck.sh ./hacapa

output: hacapa 
	bash ./runcheck.sh ./hacapa set

%: 
	(cd ..; $(MAKE) $@)

