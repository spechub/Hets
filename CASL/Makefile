# $Id$

.PHONY: check

check: capa 
	./runcheck.sh

capa: Main.hs RunParsers.hs RunMixfixParser.hs
	./ghc-call
