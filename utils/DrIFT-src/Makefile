
# utils/DrIFT-src/Makefile
# $Id$
# Author: Klaus Lüttich
# Year:   2002

# A Makefile to compile DrIFT in comfort way for two plattforms.

####################################################################
## include The uname variable
ifneq ($(MAKECMDGOALS),install)
include uname.mk
endif
####################################################################
## Some varibles, which control the compilation

HC         = ghc
PERL       = perl
####################################################################
# source
sources = DrIFT.lhs

####################################################################
### targets
solaris: DrIFT.solaris

linux: DrIFT.linux

DrIFT.$(UNAME): DrIFT.tmp
	mv DrIFT.tmp $@

install: DrIFT.linux DrIFT.solaris
	cp $^ ..

DrIFT.tmp: $(sources)
	rm -f DrIFT.tmp
	$(HC) --make -o $@ $< 
	rm -f uname.mk

### clean up
.PHONY : clean clean-bin
clean:
	rm -f DrIFT.tmp uname.mk *.hi *.o

clean-bin: clean
	rm -f DrIFT.solaris DrIFT.linux
#########################################################
uname.mk:
	rm -f $@
	$(PERL) -e  '$$un=`uname`;print "UNAME=";\
                     $$un =~ m"SunOS" && do {print "solaris"};\
                     $$un =~ m"Linux" && do {print "linux"};\
                     print "\n"' > $@
