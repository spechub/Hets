
# hetcats/Makefile
# $Id$
# Author: Klaus Lüttich
# Year:   2002



# This Makefile will compile the new hetcats system and provides also
# targets for test programs during implementation phases.

# !!! Note: This makefile is written for GNU make !!!
#           (gmake on solaris ; make on linux)

####################################################################
## Some varibles, which control the compilation

INCLUDE_PATH = ../parsec:../haterm-1.0/src:../fgl:../pretty:..:../CASL:../HasCASL:../aterm_conv

HC         = ghc
DRIFT      = ../utils/DrIFT
PERL       = perl

HC_FLAGS   = -fglasgow-exts -fallow-overlapping-instances
HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package util -package data

HC_OPTS    = $(HC_FLAGS) $(HC_PACKAGE) $(HC_INCLUDE)

####################################################################
## sources for hetcats (semi - manually produced with a perl script)
ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),real_clean)
include sources_hetcats.mk
endif
endif

objects    = $(patsubst %.lhs,%.o,$(sources:%.hs=%.o))

drifted_files = ../AS_Architecture.hs ../AS_Library.hs ../AS_Annotation.hs\
../CASL/AS_Basic_CASL.hs ../AS_Structured.hs

####################################################################
### targets

.SECONDARY : %.hs %.d 
#.PRECIOUS: sources_hetcats.mk

hetcats: $(objects)
	rm -f $@
	$(HC) -o $@ $(HC_OPTS) $(objects)

hetcats-make: hetcats.hs ../utils/create_sources.pl $(drifted_files)
	rm -f hetcats
	$(HC) --make -o hetcats $< $(HC_OPTS) 2>&1 | tee hetcats-make
	$(PERL) ../utils/create_sources.pl < hetcats-make > sources_hetcats.mk

### clean up
.PHONY : clean
clean:
	rm -f hetcats
	THIS_DIR=`pwd`;\
         for p in $(subst :, ,$(INCLUDE_PATH)) . ; do \
         cd $$p ; rm -f *.d *.hi *.o ; cd $$THIS_DIR;\
         done; \
         unset p THIS_DIR

real_clean: clean
	rm -f hetcats-make sources_hetcats.mk
####################################################################
### test targets
####################################################################
### a parser to test annotation parser and Id parsers
test_parser: ../test_parser.hs $(drifted_files)
	rm -f $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### interactive
ghci: 
	$(HC)i $(HC_OPTS)

### christian's target
casl_test_parser: ../CASL/Main.hs $(drifted_files)
	rm -f $@
	$(HC) --make -Wall -fno-warn-missing-signatures -o $@ $< $(HC_OPTS)

####################################################################
## rules for DrIFT
%.hs: %.der.hs
	$(DRIFT) $< > $@

%.lhs: %.der.lhs
	$(DRIFT) $< > $@

## compiling rules for object and interface files
%.o %.hi: %.hs
	$(HC) -c $< $(HC_OPTS)


%.o %.hi: %.lhs
	$(HC) -c $< $(HC_OPTS)

# ## compiling rules for dependencies
#%.d : %.hs
#	$(HC) -M $< $(HC_OPTS) 
#	[ -s $@ ] || rm -f $@

#%.d : %.lhs
#	$(HC) -M $< $(HC_OPTS) 
#	[ -s $@ ] || rm -f $@

%.d : %.hs
	$(HC) -M $< $(HC_OPTS) -optdep-f -optdep$@
	[ -s $@ ] || rm -f $@

%.d : %.lhs
	$(HC) -M $< $(HC_OPTS) -optdep-f -optdep$@
	[ -s $@ ] || rm -f $@


####################################################################
## Setting a global search path (for dependency files)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),real_clean)
## include every .d file in INCLUDE_PATH
-include $(objects:.o=.d)

sources_hetcats.mk: hetcats-make
endif
endif
