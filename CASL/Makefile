# $Id$

kif:
	ghc --make -Wall -i..:../ghc fromKif.hs -o fromKif

call:
	./ghc-call

%: 
	(cd test; $(MAKE) $@)
