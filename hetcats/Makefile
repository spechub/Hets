
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
PERL       = perl
DRIFT      = $(PERL) ../utils/DrIFT

HC_FLAGS   = -fglasgow-exts -fallow-overlapping-instances 
HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package util -package data

### Profiling and Warnings (only for debugging)
### Attention every module must be compiled with profiling or the linker
### cannot link the various .o files properly. So after switching on
### Profiling, do an 'gmake clean; gmake'
### If you need Profiling comment out the following line 
# HC_PROF    = -prof -auto-all -Wall

HCI_OPTS    = $(HC_FLAGS) $(HC_PACKAGE) $(HC_INCLUDE) 
HC_OPTS     = $(HCI_OPTS) $(HC_PROF)
####################################################################
## sources for hetcats (semi - manually produced with a perl script)
ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),bin_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
include sources_hetcats.mk
endif
endif
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
	rm -f hetcats-make sources_hetcats.mk
	$(HC) --make -o hetcats $< $(HC_OPTS) 2>&1 | tee hetcats-make && \
         $(PERL) ../utils/create_sources.pl hetcats-make sources_hetcats.mk
###############
### clean up
.PHONY : clean d_clean real_clean bin_clean

### removes *.hi and *.o in all include directories and the binary 'hetcats'
clean:
	THIS_DIR=`pwd`;\
         for p in $(subst :, ,$(INCLUDE_PATH)) . ; do \
         cd $$p ; rm -f *.hi *.o ; cd $$THIS_DIR;\
         done; \
         unset p THIS_DIR

### additionally removes binarys
bin_clean: clean
	rm -f hetcats
	rm -f capa
	rm -f hacapa

### additonally removes *.d (dependency files) in every include directory
### also delete *.d.bak (dependency file backups)
d_clean: clean
	THIS_DIR=`pwd`;\
         for p in $(subst :, ,$(INCLUDE_PATH)) . ; do \
         cd $$p ; rm -f *.d *.d.bak ; cd $$THIS_DIR;\
         done; \
         unset p THIS_DIR

### additionally removes the files that define the sources-variable
real_clean: d_clean bin_clean
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
	$(HC)i $(HCI_OPTS)

### christian's target
### CASL parser
capa: ../CASL/Main.hs $(drifted_files)
	rm -f $@
	$(HC) --make -Wall -fno-warn-missing-signatures -o $@ $< $(HC_OPTS)
	\cp -p $@ ../CASL/$@ 

### HasCASL parser
hacapa: ../HasCASL/Main.hs $(drifted_files)
	rm -f $@
	$(HC) --make -Wall -fno-warn-missing-signatures -o $@ $< $(HC_OPTS)
	\cp -p $@ ../HasCASL/$@ 

####################################################################
## Preparing the version of HetCATS
Version.hs: Version.in version_nr
	$(PERL) ../utils/build_version.pl version_nr < Version.in > $@

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

## compiling rules for dependencies
%.d : %.hs
	$(HC) -M $< $(HC_OPTS) -optdep-f -optdep$@

%.d : %.lhs
	$(HC) -M $< $(HC_OPTS) -optdep-f -optdep$@

####################################################################
## Setting a global search path (for dependency files)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
## include every .d file in INCLUDE_PATH
-include $(objects:.o=.d)

sources_hetcats.mk: hetcats-make Version.hs
endif
endif
endif
endif
