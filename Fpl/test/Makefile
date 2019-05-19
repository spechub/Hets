# $Id$

.PHONY: check

check: hets
	../../hets -v2 -o pp.dol,th specs.het
	../../hets -v2 -o pp.dol,th specs.pp.dol

%:
	(cd ../..; $(MAKE) $@)
