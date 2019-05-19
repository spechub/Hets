# $Id$

.PHONY: check

check: hets
	../../hets -v2 -o pp.dol,th Try?.het
	../../hets -v2 -o pp.dol,th Try?.pp.dol

%:
	(cd ../..; $(MAKE) $@)
