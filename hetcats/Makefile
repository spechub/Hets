
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

INCLUDE_PATH = ../parsec:../haterm-1.0/src:../fgl:../pretty:..:../CASL:../HasCASL:../aterm_conv:../ghc

HC         = ghc
PERL       = perl
DRIFT      = $(PERL) ../utils/DrIFT
AG         = $(PERL) ../utils/ag
HADDOCK    = $(PERL) ../utils/haddock

HC_FLAGS   = -fglasgow-exts -fallow-overlapping-instances -Wall
HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package data

AG_FLAGS   = -mdcfs

### Profiling and Warnings (only for debugging)
### Attention every module must be compiled with profiling or the linker
### cannot link the various .o files properly. So after switching on
### Profiling, do an 'gmake clean; gmake'
### If you need Profiling comment out the following line 
#HC_PROF    = -prof -auto-all -Wall 

HCI_OPTS    = $(HC_FLAGS) $(HC_PACKAGE) $(HC_INCLUDE) 
HC_OPTS     = $(HCI_OPTS) $(HC_PROF)

### list of directories to run checks in
TESTDIRS    = ../CASL ../test

####################################################################
## sources for hetcats (semi - manually produced with a perl script)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),bin_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),distclean)
include sources_hetcats.mk
endif
endif
endif
endif
endif

objects    = $(patsubst %.lhs,%.o,$(sources:%.hs=%.o))

drifted_files = ../AS_Architecture.hs ../AS_Library.hs ../AS_Annotation.hs\
../CASL/AS_Basic_CASL.hs ../AS_Structured.hs

# this variable holds the modules that should be documented
# the imported parsec library is not included!
doc_sources = $(filter-out ../parsec/% ,$(sources))

####################################################################
### targets

.PHONY : clean d_clean real_clean bin_clean check
.SECONDARY : %.hs %.d 
#.PRECIOUS: sources_hetcats.mk

hetcats: $(objects)
	$(RM) $@
	$(HC) -o $@ $(HC_OPTS) $(objects)

hetcats-make: hetcats.lhs ../utils/create_sources.pl $(drifted_files)
	$(RM) hetcats-make sources_hetcats.mk
	$(HC) --make -o hetcats $< $(HC_OPTS) 2>&1 | tee hetcats-make && \
         $(PERL) ../utils/create_sources.pl hetcats-make sources_hetcats.mk

###############################
### TAGS files for (x)emacs 
# load them with "M-x" "visit-tags-table" from
# "HetCATS/hetcats/hetcats.TAGS"
# use "M-." to search for a tag
# !!Beware this is somewhat instable, because it uses an absolute path!!
hetcats.TAGS: $(sources) 
	/home/ger/linux/ghc-5.04.2/bin/i386-unknown-linux/hasktags \
	  $(sources); mv TAGS $@; mv tags hetcats.tags

###############################
### Documentation via haddock
doc: docs/index.html ../utils/hd-lib

docs/index.html: $(doc_sources)
	$(HADDOCK) $(doc_sources) -o docs -h \
          -t 'HetCATS -- a heterogenous CASL tool set'

###############
### clean up

### removes *.hi and *.o in all include directories
clean:
	for p in $(subst :, ,$(INCLUDE_PATH)) . ; do \
	(cd $$p ; $(RM) *.hi *.hi.bak *.o) ; done

### additionally removes binaries
bin_clean: clean
	$(RM) hetcats
	$(RM) ../CASL/capa
	$(RM) ../HasCASL/hacapa

### additonally removes *.d (dependency files) in every include directory
### also delete *.d.bak (dependency file backups)
d_clean: clean
	for p in $(subst :, ,$(INCLUDE_PATH)) . ; do \
	(cd $$p ; $(RM) *.d *.d.bak) ; done

### additionally removes the files that define the sources-variable
real_clean: d_clean bin_clean
	$(RM) hetcats-make sources_hetcats.mk

### additionally removes files not in CVS tree
distclean: real_clean
	$(RM) Version.hs
	$(RM) $(drifted_files)

####################################################################
### test targets
####################################################################

### a parser to test annotation parser and Id parsers
test_parser: ../test_parser.hs $(drifted_files)
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS) 

### interactive
ghci: 
	$(HC)i $(HCI_OPTS)

### christian's target
### CASL parser
capa: ../CASL/capa

../CASL/capa: ../CASL/capa.lhs $(drifted_files) ../CASL/*.hs
	$(RM) $@
	$(HC) --make -o ../CASL/$@ $< $(HC_OPTS)

### HasCASL parser
hacapa: ../HasCASL/hacapa

../HasCASL/hacapa: ../HasCASL/hacapa.lhs $(drifted_files) ../HasCASL/*.hs 
	$(RM) $@
	$(HC) --make -o ../HasCASL/$@ $< $(HC_OPTS)

### HetCASL parser
hetpa: ../hetpa.hs $(drifted_files) ../*.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### run tests in other directories
check: hetcats
	for i in $(TESTDIRS); do $(MAKE) -C $$i check; done

####################################################################
## Preparing the version of HetCATS
Version.hs: Version.in version_nr
	$(PERL) ../utils/build_version.pl version_nr < Version.in > $@

## two hardcoded dependencies for a correct generation of Version.hs
Options.hs: Version.hs
hetcats.lhs: Version.hs
####################################################################
## rules for DrIFT

%.hs: %.ag.hs
	$(AG) $<

%.hs: %.der.hs
	$(DRIFT) $< > $@

%.hs: %.ag
	$(AG) $< -o $@

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
ifneq ($(MAKECMDGOALS),distclean)
## include every .d file in INCLUDE_PATH
-include $(objects:.o=.d)

sources_hetcats.mk: hetcats-make Version.hs
endif
endif
endif
endif
endif
