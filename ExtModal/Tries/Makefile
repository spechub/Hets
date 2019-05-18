# $Id$

.PHONY: check

check:.dols
	../...dols -v2 -o pp.dol,th Try?.het
	../...dols -v2 -o pp.dol,th Try?.pp.het

%:
	(cd ../..; $(MAKE) $@)
