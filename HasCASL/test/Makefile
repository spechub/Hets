# $Id$

.PHONY: check

check: ../hacapa
	bash runcheck.sh ../hacapa

../hacapa: ../*.hs
	(cd ..; ghc-call)

hacapa:
	$(MAKE) ../hacapa

output: 
	bash runcheck.sh ../hacapa set
