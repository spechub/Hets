# $Id$

.PHONY: check

check: annos Common/testxpath Common/testxupdate
	./runcheck.sh ../annos
	../testxpath < XPath.examples > temp1
	../testxpath < temp1 > temp2
	diff temp1 temp2
	../testxupdate < diff.AddingImports.decomposed.xml > temp

output: annos
	./runcheck.sh ../annos set

%:
	(cd ../..; $(MAKE) $@)

