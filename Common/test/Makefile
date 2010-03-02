# $Id$

.PHONY: check

check: annos Common/testxpath
	./runcheck.sh ../annos
	../testxpath < XPath.examples > temp1
	../testxpath < temp1 > temp2
	diff temp1 temp2

output: annos
	./runcheck.sh ../annos set

%:
	(cd ../..; $(MAKE) $@)

