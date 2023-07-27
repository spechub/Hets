# $Id$

.PHONY: check

check: hets_available
	HETS_MAGIC=../../magic/hets.magic ../../hets -v2 -o pp.dol,th Try?.dol
	HETS_MAGIC=../../magic/hets.magic ../../hets -v2 -o pp.dol,th Try?.pp.dol

%:
	(cd ../..; $(MAKE) $@)
