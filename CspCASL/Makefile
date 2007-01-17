### Makefile --- CSP-CASL parser in hets framework

## Author: a.m.gimblett@swan.ac.uk
## Version: $Id$
## Keywords: 
## X-URL: 

GHCINCLUDES	=	..:../ghc:../Common:../CASL

GHCOPTS		=	--make -fglasgow-exts -Wall -i$(GHCINCLUDES)

BINS		=	c3po print

SOURCES		=	Main.hs AS_CSP_CASL.hs CCKeywords.hs CCLexer.hs \
                        CCToken.hs Parse_hugo.hs

.PHONY:			test

default:		c3po

all:			$(BINS)

clean:
			@find . -name '*~' -exec rm -vf {} ';'
			@find . -name '*.o' -exec rm -vf {} ';'
			@find . -name '*.hi' -exec rm -vf {} ';'
			@find . -name '*.der.hs' -exec rm -vf {} ';'
			@find . -name 'ATC*.hs' -exec rm -vf {} ';'
			@rm -vf $(BINS)


ccparse:
			ghc -o ccparse $(GHCOPTS) ccparse.hs

StatAnaCSP.o:
			ghc $(GHCOPTS) StatAnaCSP.hs

c3po:			$(SOURCES)
			ghc $(GHCOPTS) -o c3po Main.hs #MixfixParser.hs 

print:			print_csp.hs
			ghc $(GHCOPTS) -o print print_csp.hs

test:			c3po
			./c3po test/amg.csp-casl
#			./c3po test/*.csp-casl

### Makefile ends here
