

# A Makefile to compile inlineAxioms in a comfortable way for various plattforms.

####################################################################
## include The uname variable
ifneq ($(MAKECMDGOALS),install)
include uname.mk
endif
####################################################################
## Some variables, which control the compilation

INCLUDE_PATH = ../..:../../ghc:../../hetcats
HC_FLAGS   = -Wall  

HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package-conf ../../../uni/uni-package.conf  -package uni-davinci \
             -package uni-server

HCI_OPTS    = $(HC_FLAGS) $(HC_PACKAGE) $(HC_INCLUDE)
HC_OPTS     = $(HCI_OPTS) $(HC_PROF)

#include ../../Makefile

HC         = ghc
#PERL       = perl
####################################################################
# source
sources = InlineAxioms.hs

####################################################################
### targets
macintosh: inlineAxioms.macintosh

solaris: inlineAxioms.solaris

linux: inlineAxioms.linux

inlineAxioms.$(UNAME): inlineAxioms.tmp
	mv inlineAxioms.tmp $@

install: inlineAxioms.$(UNAME)  #linux inlineAxioms.solaris inlineAxioms.macintosh
	cp $^ ../inlineAxioms

inlineAxioms.tmp: $(sources)
	rm -f inlineAxioms.tmp
	$(HC) --make -o $@ $< $(HC_OPTS) 
	rm -f uname.mk

### clean up
.PHONY : clean clean-bin
clean:
	rm -f inlineAxioms.tmp uname.mk *.hi *.o

clean-bin: clean
	rm -f inlineAxioms.solaris inlineAxioms.linux
#########################################################
uname.mk:
	rm -f $@
	$(PERL) -e  '$$un=`uname`;print "UNAME=";\
                     $$un =~ m"Darwin" && do {print "macintosh"};\
                     $$un =~ m"SunOS" && do {print "solaris"};\
                     $$un =~ m"Linux" && do {print "linux"};\
                     print "\n"' > $@
