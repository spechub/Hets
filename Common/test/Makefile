# $Id$

.PHONY: check

check: ../test_parser
	../test_parser Annotations.casl

output: ../test_parser
	../test_parser Annotations.casl > Annotations.casl.output

%: 
	(cd ..; $(MAKE) $@)

