# $Id$

.PHONY: check

check: annos
	bash runcheck.sh ../annos

output: annos
	bash runcheck.sh ../annos set

%: 
	(cd ../..; $(MAKE) $@)

