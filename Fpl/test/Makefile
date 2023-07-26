# $Id$

.PHONY: check

check: hets_available
	HETS_MAGIC=../../magic/hets.magic ../../hets -v2 -o pp.dol,th specs.dol
	HETS_MAGIC=../../magic/hets.magic ../../hets -v2 -o pp.dol,th specs.pp.dol

%:
	(cd ../..; $(MAKE) $@)
