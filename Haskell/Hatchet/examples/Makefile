# $Id$

.PHONY: check

check: hana
	./runcheck.sh ../../hana

output: hana
	./runcheck.sh ../../hana set

%: 
	(cd ../../..; $(MAKE) $@)

