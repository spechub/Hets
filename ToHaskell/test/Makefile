# $Id$

.PHONY: check

check: translateAna
	./runcheck.sh ../translateAna

output: translateAna
	./runcheck.sh ../translateAna set

translateAna:
	if test ! -x ../translateAna; then (cd ..; ./ghc-call); fi
	if test ! -x ../../HasCASL/hacapa; \
               then (cd ../../HasCASL; ./ghc-call); fi
	if test ! -x ../../Haskell/Hatchet/hatch; \
               then (cd ../../Haskell/Hatchet; ./ghc-call); fi

%: 
	(cd ../..; $(MAKE) $@)

