### Makefile --- CSP-CASL parser in hets framework

## Author: a.m.gimblett@swan.ac.uk
## Version: $Id$
## Keywords: 
## X-URL: 

GHCINCLUDES	=	..

GHCOPTS		=	-Wall -fglasgow-exts -package base -package parsec -package fgl -i$(GHCINCLUDES)

BINS		=	testwrap

SOURCES		=	AS_CspCASL.hs \
			AS_CspCASL_Process.hs \
			CspCASL_Keywords.hs \
			Logic_CspCASL.hs \
			Parse_CspCASL.hs \
			Parse_CspCASL_Process.hs \
			Print_CspCASL.hs \
			SignCSP.hs \
			StatAnaCSP.hs \
			testwrap.hs

.PHONY:			test

default:		test

all:			$(BINS)

clean:
			@find . -name '*~' -exec rm -vf {} ';'
			@find . -name '*.o' -exec rm -vf {} ';'
			@find . -name '*.hi' -exec rm -vf {} ';'
			@find . -name '*.der.hs' -exec rm -vf {} ';'
			@find . -name 'ATC*.hs' -exec rm -vf {} ';'
			@rm -vf $(BINS)

nuke:			clean

testwrap:		$(SOURCES)
			gmake -C .. CspCASL/testwrap

test:			testwrap
			./testwrap test/amg.csp-casl
