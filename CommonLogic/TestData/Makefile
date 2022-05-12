# $Id$

.PHONY: check

check: hets_available
	HETS_MAGIC=../../magic/hets.magic ../../hets -v2 -o th *.clf
	HETS_MAGIC=../../magic/hets.magic ../../hets -v2 -o pp.dol,th *.dol

%:
	(cd ../..; $(MAKE) $@)
