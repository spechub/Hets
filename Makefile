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
CLEAN_PATH = Common:Logic:CASL:Syntax:Static:GUI:HasCASL:Haskell:Haskell/Language:Modal:CspCASL:ATC:ToHaskell:Proofs:Comorphisms:$(INCLUDE_PATH):Haskell/Hatchet

DRIFT_ENV = DERIVEPATH='.:ghc:hetcats:/home/linux-bkb/ghc/ghc-latest/lib/ghc-6.0.1/imports'

HC         = ghc
PERL       = perl
HAPPY      = happy
DRIFT      = $(DRIFT_ENV) $(PERL) utils/DrIFT
AG         = $(PERL) utils/ag
HADDOCK    = $(PERL) utils/haddock

HC_FLAGS   = -fglasgow-exts -fallow-overlapping-instances -Wall
# please remove '-O2' if compilation lasts to long on your system
# but please don't commit to cvs server

HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package-conf ../uni/uni-package.conf  -package uni-davinci \
             -package uni-server

AG_FLAGS   = -mdcfs

### Profiling and Warnings (only for debugging)
### Attention every module must be compiled with profiling or the linker
### cannot link the various .o files properly. So after switching on
### Profiling, do an 'gmake clean; gmake'
### If you need Profiling comment out the following line 
#HC_PROF    = -prof -auto-all 

HCI_OPTS    = $(HC_FLAGS) $(HC_PACKAGE) $(HC_INCLUDE)
HC_OPTS     = $(HCI_OPTS) $(HC_PROF)
DRIFT_OPTS  = +RTS -K10 -RTS

### list of directories to run checks in
TESTDIRS    = CASL HasCASL test

####################################################################
## sources for hetcats (semi - manually produced with a perl script)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),bin_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),distclean)
ifneq ($(MAKECMDGOALS),genRules)
ifneq ($(MAKECMDGOALS),apache_doc)
ifneq ($(MAKECMDGOALS),clean_genRules)
ifneq ($(MAKECMDGOALS),atctest2)
include sources_hetcats.mk
endif
endif
endif
endif
endif
endif
endif
endif
endif

objects    = $(patsubst %.lhs,%.o,$(sources:%.hs=%.o))

drifted_files = Syntax/AS_Architecture.hs Syntax/AS_Library.hs\
    Common/AS_Annotation.hs CASL/AS_Basic_CASL.hs Syntax/AS_Structured.hs \
    $(gendrifted_files)

genrule_header_files = $(wildcard ATC/*.header.hs)

genrule_files = Common/Lib/Graph.hs Common/Id.hs Common/Result.hs \
                Common/AS_Annotation.der.hs Common/Named.hs \
                Syntax/AS_Structured.der.hs Syntax/AS_Architecture.der.hs \
                Common/GlobalAnnotations.hs Syntax/AS_Library.der.hs \
                CASL/Sublogic.hs \
                CASL/Morphism.hs CASL/StaticAna.hs CASL/AS_Basic_CASL.der.hs \
                HasCASL/Le.hs HasCASL/As.hs HasCASL/Symbol.hs \
                HasCASL/Morphism.hs HasCASL/AsToIds.hs \
                CspCASL/AS_CSP_CASL.hs \
                Static/DevGraph.hs \
                Haskell/Hatchet/AnnotatedHsSyn.hs \
                Haskell/Hatchet/MultiModuleBasics.hs \
                Haskell/Hatchet/HsSyn.hs \
                Haskell/Hatchet/Representation.hs\
                Haskell/Hatchet/Class.hs Haskell/Hatchet/KindInference.hs \
                Haskell/Hatchet/Env.hs 

gendrifted_files = ATC/Graph.hs ATC/Id.hs ATC/Result.hs ATC/AS_Annotation.hs \
                   ATC/Named.hs \
                   ATC/AS_Library.hs ATC/GlobalAnnotations.hs \
                   ATC/AS_Structured.hs ATC/AS_Architecture.hs \
                   ATC/DevGraph.hs \
                   CASL/ATC_CASL.hs Haskell/ATC_Haskell.hs \
                   HasCASL/ATC_HasCASL.hs CspCASL/ATC_CspCASL.hs 

generated_rule_files = $(patsubst %.hs,%.der.hs,$(gendrifted_files))

happy_files = Haskell/Language/Parser.hs Haskell/Hatchet/HsParser.hs

# this variable holds the modules that should be documented
# the imported parsec library is not included!
doc_sources = $(filter-out Nothing/Nothing% ,$(sources))

####################################################################
### targets

.PHONY : clean d_clean real_clean bin_clean check hetana hetpa hetdg \
         clean_genRules genRules

.SECONDARY : %.hs %.d $(generated_rule_files)
#.PRECIOUS: sources_hetcats.mk

all: hets

hets: $(sources)
	$(HC) --make -o $@ hets.hs $(HC_OPTS)

hets-opt: $(sources)
	$(MAKE) real_clean
	$(MAKE) hets-optimized

hets-optimized: $(sources)
	$(HC) --make -O -o $@ hets.hs $(HC_OPTS)

hets-old: $(objects)
	$(RM) $@
	$(HC) -o hets $(HC_OPTS) $(objects)

hetcats-make: hets.hs utils/create_sources.pl $(drifted_files) $(happy_files)
	$(RM) hetcats-make sources_hetcats.mk
	$(HC) --make -o hets $< $(HC_OPTS) 2>&1 | tee hetcats-make 

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
          --read-interface=http://www.haskell.org/ghc/docs/latest/html/libraries/base,/home/linux-bkb/ghc/ghc-6.0.1/share/ghc-6.0.1/html/base/base.haddock \
          -t 'hets -- a heterogenous Specification (CASL) tool set'

apache_doc:
	cvs up -d
	$(MAKE) distclean
	$(MAKE) hetcats-make
	$(RM) docs/*.html 
	$(MAKE) doc
	$(MAKE) post_doc4apache

post_doc4apache:
	$(PERL) utils/post_process_docs.pl docs \
            'Common.Lib.Map.html:Common.Lib._Map.html'
	mv docs/* a-docs/

#############################
### ATC DrIFT-rule generation

genRules: $(generated_rule_files)

$(generated_rule_files): $(genrule_files)# $(genrule_header_files)
	$(MAKE) clean_genRules
	$(foreach file,$(atc_files),$(gen_atc_files))
	utils/genRules -r $(rule) -o CASL    -h ATC/CASL.header.hs $(casl_files)
	utils/genRules -r $(rule) -o HasCASL -h ATC/HasCASL.header.hs $(hascasl_files)
	utils/genRules -r $(rule) -o CspCASL -h ATC/CspCASL.header.hs $(cspcasl_files)
	utils/genRules -r $(rule) -o Haskell -h ATC/Haskell.header.hs $(haskell_files)

rule = ShATermConvertible

gen_atc_files = if [ -f ATC/$(basename $(basename $(notdir $(file)))).header.hs ]; then \
                   utils/genRules -r $(rule) -o ATC -h ATC/$(basename $(basename $(notdir $(file)))).header.hs $(file); \
                else \
                   utils/genRules -r $(rule) -o ATC $(file); \
                fi ;

atc_files := $(filter-out CASL/% HasCASL/% CspCASL/% Haskell/% ,$(genrule_files))
casl_files := $(filter CASL/% ,$(genrule_files))
hascasl_files := $(filter HasCASL/% ,$(genrule_files))
cspcasl_files := $(filter CspCASL/% ,$(genrule_files))
haskell_files := $(filter Haskell/%,$(genrule_files))

clean_genRules: 
	$(RM) $(generated_rule_files)

###############
### clean up

### removes *.hi and *.o in all include directories
clean: bin_clean
	for p in $(subst :, ,$(CLEAN_PATH)) . ; do \
	(cd $$p ; $(RM) *.hi *.o) ; done

### remove binaries
bin_clean: 
	$(RM) hets
	$(RM) test_parser
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

### additionally removes files not in CVS tree
distclean: real_clean clean_genRules d_clean
	$(RM) hetcats/Version.hs
	$(RM) $(drifted_files)
	$(RM) $(happy_files)

####################################################################
### test targets
####################################################################

### a parser to test annotation parser and Id parsers
test_parser: Common/test_parser

Common/test_parser: Common/test_parser.hs Common/AS_Annotation.der.hs
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

### ATC test system
atctest: ATC/ATCTest.hs ATC/*.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

atctest2: ATC/ATCTest2.hs Common/SimpPretty.hs Common/ATerm/*.hs Common/Lib/*.hs
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### ATerm.Lib test system
atermlibtest: Common/ATerm/ATermLibTest.hs Common/ATerm/*.hs Common/SimpPretty.hs
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
hetcats/Options.hs hetcats/WriteFn.hs hetcats/ReadFn.hs: hetcats/Version.hs
hets.hs: hetcats/Version.hs
####################################################################
## rules for DrIFT

%.hs: %.ly
	$(HAPPY) $<

#%.hs: %.ag.hs
#	$(AG) $<

%.hs: %.der.hs
	$(DRIFT) $(DRIFT_OPTS) $< > $@

#%.hs: %.ag
#	$(AG) $< -o $@

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
ifneq ($(MAKECMDGOALS),genRules)
ifneq ($(MAKECMDGOALS),clean_genRules)
ifeq  ($(MAKECMDGOALS),hets-old)
## include every .d file in INCLUDE_PATH
-include $(objects:.o=.d)
endif

sources_hetcats.mk: hetcats-make hetcats/Version.hs hets.hs utils/create_sources.pl $(drifted_files) $(happy_files)
	$(PERL) utils/create_sources.pl hetcats-make sources_hetcats.mk
endif
endif
endif
endif
endif
endif
endif
