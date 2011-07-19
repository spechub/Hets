# $Id$

.PHONY: check

check: hets
	../../hets -v2 -o th *.clf
	../../hets -v2 -o pp.het,th *.het

%:
	(cd ../..; $(MAKE) $@)
