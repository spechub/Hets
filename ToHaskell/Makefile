
.PHONY: check

check: hapa 
	bash ./runcheck.sh ../Haskell/hapa

output: hapa 
	bash ./runcheck.sh ../Haskell/hapa set

%: 
	(cd ..; $(MAKE) $@)

