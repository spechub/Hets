# $Id$

.PHONY: check

check:.dols
	../...dols -v2 -o pp.dol,th specs.het
	../...dols -v2 -o pp.dol,th specs.pp.het

%:
	(cd ../..; $(MAKE) $@)
