
# hetcats/Makefile
# $Id$
# Author: Klaus Lüttich
# Year:   2003

# This Makefile will compile the new hetcats system and provides also
# targets for test programs during implementation phases.

# !!! Note: This makefile is written for GNU make !!!
#           (gmake on solaris ; make on linux)

####################################################################
## Some varibles, which control the compilation

INCLUDE_PATH = ghc:hetcats
COMMONLIB_PATH = Common/Lib:Common/Lib/Parsec:Common/ATerm
CLEAN_PATH = Common:Logic:CASL:Syntax:Static:GUI:HasCASL:Haskell:Haskell/Language:Modal:CspCASL:$(INCLUDE_PATH)

HC         = ghc
PERL       = perl
HAPPY      = happy
DRIFT      = $(PERL) utils/DrIFT
AG         = $(PERL) utils/ag
HADDOCK    = haddock

HC_FLAGS   = -fglasgow-exts -fallow-overlapping-instances -Wall
HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package-conf ../uni/uni-package.conf  -package uni-davinci -package uni-server

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
TESTDIRS    = Common/test CASL/test HasCASL/test ToHaskell test

####################################################################
## sources for hetcats (semi - manually produced with a perl script)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),bin_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),distclean)
ifneq ($(MAKECMDGOALS),apache_doc)
include sources_hetcats.mk
endif
endif
endif
endif
endif
endif

objects    = $(patsubst %.lhs,%.o,$(sources:%.hs=%.o))

drifted_files = Syntax/AS_Architecture.hs Syntax/AS_Library.hs\
    Common/AS_Annotation.hs CASL/AS_Basic_CASL.hs Syntax/AS_Structured.hs

happy_files = Haskell/Language/Parser.hs

# this variable holds the modules that should be documented
# the imported parsec library is not included!
doc_sources = $(filter-out Nothing/Nothing% ,$(sources))

####################################################################
### targets

.PHONY : clean d_clean real_clean bin_clean check hetana hetpa hetdg hets
.SECONDARY : %.hs %.d 
#.PRECIOUS: sources_hetcats.mk

all: $(sources)
	$(HC) --make -o hets hets.hs $(HC_OPTS)

hets: $(sources)
	$(HC) --make -o $@ hets.hs $(HC_OPTS)

hets-old: $(objects)
	$(RM) $@
	$(HC) -o hets $(HC_OPTS) $(objects)

hetcats-make: hets.hs utils/create_sources.pl $(drifted_files) $(happy_files)
	$(RM) hetcats-make sources_hetcats.mk
	$(HC) --make -o hets $< $(HC_OPTS) 2>&1 | tee hetcats-make && \
         $(PERL) utils/create_sources.pl hetcats-make sources_hetcats.mk

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
doc: docs/index.html utils/hd-lib

docs/index.html: $(doc_sources)
	$(HADDOCK) $(doc_sources) -o docs -h \
          -i/home/linux-bkb/ghc/ghc-6.0/share/ghc-6.0/html/base,/home/linux-bkb/ghc/ghc-6.0/share/ghc-6.0/html/base/base.haddock \
          -t 'hets -- a heterogenous Specification (CASL) tool set'

apache_doc:
	cvs up -d
	$(MAKE) distclean
	$(MAKE) hetcats-make
	$(RM) docs/*.html 
	$(MAKE) doc
	$(PERL) utils/post_process_docs.pl docs \
            'Common.Lib.Map.html:Common.Lib._Map.html'
	mv docs/* a-docs/

###############
### clean up

### removes *.hi and *.o in all include directories
clean: bin_clean
	for p in $(subst :, ,$(CLEAN_PATH)) . ; do \
	(cd $$p ; $(RM) *.hi *.o) ; done

### remove binaries
bin_clean: 
	$(RM) hets
	$(RM) Common/annos
	$(RM) Common/test_parser
	$(RM) CASL/capa
	$(RM) HasCASL/hacapa
	$(RM) Haskell/hapa
	$(RM) Haskell/wrap
	$(RM) Syntax/hetpa
	$(RM) Static/hetana
	$(RM) Static/hetana
	$(RM) GUI/hetdg
	$(RM) hetpa
	$(RM) hetana
	$(RM) hetdg

### additonally removes *.d (dependency files) in every include directory
### also delete *.d.bak (dependency file backups)
d_clean: clean
	for p in $(subst :, ,$(CLEAN_PATH)) . ; do \
	(cd $$p ; $(RM) *.d *.d.bak) ; done

### remove files also in own libraries
lib_clean: clean
	for p in $(subst :, ,$(COMMONLIB_PATH)) . ; do \
	(cd $$p ; $(RM) *.hi *.d *.o) ; done

### additionally removes the files that define the sources-variable
real_clean: bin_clean lib_clean
	$(RM) hetcats-make sources_hetcats.mk
	$(RM) AS_*.hs

### additionally removes files not in CVS tree
distclean: real_clean
	$(RM) hetcats/Version.hs
	$(RM) $(drifted_files)
	$(RM) Haskell/Language/Parser.hs

####################################################################
### test targets
####################################################################

### a parser to test annotation parser and Id parsers
test_parser: Common/test_parser

Common/test_parser: Common/test_parser.hs Common/AS_Annotation.der.hs
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS) 

annos: Common/annos

Common/annos: Common/annos.hs Common/AS_Annotation.der.hs
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS) 

### interactive
ghci: 
	$(HC)i $(HCI_OPTS)

### christian's target
### CASL parser
capa: CASL/capa

CASL/capa: CASL/capa.lhs Common/*.hs CASL/*.hs
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### HasCASL parser
hacapa: HasCASL/hacapa

HasCASL/hacapa: HasCASL/hacapa.lhs CASL/capa HasCASL/*.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### Haskell parser
hapa: Haskell/hapa

Haskell/hapa: Haskell/hapa.lhs Haskell/*.hs Haskell/Language/*.hs $(happy_files)
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### Haskell wrap parser
wrap: Haskell/wrap

Haskell/wrap: Haskell/wrap.lhs Haskell/*.hs
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### HetCASL parser
hetpa: Syntax/hetpa.hs Syntax/*.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### HetCASL parser
hetana: Static/hetana.hs Static/*.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### HetCASL with dev graph
hetdg: GUI/hetdg.hs $(drifted_files) *.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)  -package-conf ../uni/uni-package.conf  -package uni-davinci -package uni-server


### run tests in other directories
check: hetcats
	for i in $(TESTDIRS); do $(MAKE) -C $$i check; done

####################################################################
## Preparing the version of HetCATS
hetcats/Version.hs: hetcats/Version.in version_nr
	$(PERL) utils/build_version.pl version_nr < hetcats/Version.in > $@

## two hardcoded dependencies for a correct generation of Version.hs
hetcats/Options.hs: hetcats/Version.hs
hets.hs: hetcats/Version.hs
####################################################################
## rules for DrIFT

%.hs: %.ly
	$(HAPPY) $<

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

sources_hetcats.mk: hetcats-make hetcats/Version.hs
endif
endif
endif
endif
endif
