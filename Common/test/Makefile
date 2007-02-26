# $Id$

.PHONY: check

check: annos
	./runcheck.sh ../annos

output: annos
	./runcheck.sh ../annos set

%:
	(cd ../..; $(MAKE) $@)

