# $Id$

.PHONY: check

check: ../../hets
	../../hets -v2 -o pp.het,th specs.het
	../../hets -v2 -o pp.het,th specs.pp.het

%:
	(cd ../..; $(MAKE) $@)
