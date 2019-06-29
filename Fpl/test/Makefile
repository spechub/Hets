# $Id$

.PHONY: check

check: hets
	../../hets -v2 -o pp.dol,th specs.dol
	../../hets -v2 -o pp.dol,th specs.pp.dol

%:
	(cd ../..; $(MAKE) $@)
