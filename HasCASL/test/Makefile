# $Id$

.PHONY: check

check: hacapa
	bash ./runcheck.sh ../hacapa

output: 
	bash ./runcheck.sh ../hacapa set

%: 
	(cd ../..; $(MAKE) $@)
