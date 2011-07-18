# $Id$

.PHONY: check

check: hets
	../../hets -v2 -o pp.het,th Try?.het
	../../hets -v2 -o pp.het,th Try?.pp.het

%:
	(cd ../..; $(MAKE) $@)
