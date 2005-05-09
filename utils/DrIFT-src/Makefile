
# utils/DrIFT-src/Makefile
# $Id$
# Author: Klaus Lüttich
# Year:   2002

# A Makefile to compile DrIFT in a comfortable way for various plattforms.

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
sources = DrIFT.hs

####################################################################
### targets
DrIFT.$(UNAME): DrIFT.tmp
	mv DrIFT.tmp $@

install: DrIFT.$(UNAME)
	cp $^ ..

DrIFT.tmp: $(sources)
	rm -f DrIFT.tmp
	$(HC) -Wall --make -o $@ $< 
	rm -f uname.mk

### clean up
.PHONY : clean clean-bin
clean:
	rm -f DrIFT.tmp uname.mk *.hi *.o

clean-bin: clean
	rm -f DrIFT.solaris DrIFT.linux DrIFT.macintosh
#########################################################
uname.mk:
	rm -f $@
	$(PERL) -e  '$$un=`uname`;print "UNAME=";\
                     $$un =~ m"Darwin" && do {print "macintosh"};\
                     $$un =~ m"SunOS" && do {print "solaris"};\
                     $$un =~ m"Linux" && do {print "linux"};\
                     print "\n"' > $@
