

# A Makefile to compile genRules in a comfortable way for various plattforms.

####################################################################
## include The uname variable
ifneq ($(MAKECMDGOALS),install)
include uname.mk
endif
####################################################################
## Some variables, which control the compilation

HC         = ghc
PERL       = perl
####################################################################
# source
sources = GenerateRules.hs

####################################################################
### targets
macintosh: genRules.macintosh

solaris: genRules.solaris

linux: genRules.linux

genRules.$(UNAME): genRules.tmp
	mv genRules.tmp $@

install: genRules.linux genRules.solaris genRules.macintosh
	cp $^ ..

genRules.tmp: $(sources)
	rm -f genRules.tmp
	$(HC) --make -package text -i../..:../DrIFT-src -o $@ $< 
	rm -f uname.mk

### clean up
.PHONY : clean clean-bin
clean:
	rm -f genRules.tmp uname.mk *.hi *.o

clean-bin: clean
	rm -f genRules.solaris genRules.linux
#########################################################
uname.mk:
	rm -f $@
	$(PERL) -e  '$$un=`uname`;print "UNAME=";\
                     $$un =~ m"Darwin" && do {print "macintosh"};\
                     $$un =~ m"SunOS" && do {print "solaris"};\
                     $$un =~ m"Linux" && do {print "linux"};\
                     print "\n"' > $@
