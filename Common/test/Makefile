# $Id$

.PHONY: check

check: annos Common/testxpath Common/testxupdate Common/testxmldiff
	./runcheck.sh ../annos
	../testxpath < XPath.examples > temp1
	../testxpath < temp1 > temp2
	diff temp1 temp2
	../testxupdate < diff.AddingImports.decomposed.xml > temp
	../testxmldiff t1.xml t2.xml > temp
	../testxmldiff t2.xml t1.xml > temp
	../testxmldiff t2.xml t2.xml

output: annos
	./runcheck.sh ../annos set

%:
	(cd ../..; $(MAKE) $@)
