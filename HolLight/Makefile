# $Id$

.PHONY: check

check: hets
	../hets -v2 -t HolLight2Isabelle -o thy example_binom.hol
	../utils/nightly/runisabelle.sh *.thy >& hol2isa.log

%:
	(cd ..; $(MAKE) $@)
