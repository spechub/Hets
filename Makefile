# hetcats/Makefile
# $Header$
# Author: (c) Klaus Lüttich, Christian Maeder, Uni Bremen 2002-2004
# Year:   2004

# This Makefile will compile the new hetcats system and provides also
# targets for test programs during implementation phases.

# !!! Note: This makefile is written for GNU make !!!
#           (gmake on solaris ; make on linux)

####################################################################
## Some varibles, which control the compilation

INCLUDE_PATH = ghc:hetcats
COMMONLIB_PATH = Common/Lib:Common/Lib/Parsec:Common/ATerm
CLEAN_PATH = utils/DrIFT-src:utils/GenerateRules:utils/inlineAxioms:Common:Logic:CASL:CASL/CCC:Syntax:Static:GUI:HasCASL:Haskell:Modal:CoCASL:COL:CspCASL:ATC:ToHaskell:Proofs:Comorphisms:Isabelle:$(INCLUDE_PATH):Haskell/Hatchet

## set ghc imports properly for your system
LINUX_IMPORTS = $(wildcard /home/linux-bkb/ghc/ghc-latest/lib/ghc-*/imports)
DRIFT_ENV = DERIVEPATH='.:ghc:hetcats:${LINUX_IMPORTS}:${GHC_IMPORTS}'

# override on commandline for other architectures
INSTALLDIR = /home/www/agbkb/forschung/formal_methods/CoFI/hets/`utils/sysname.sh`

DRIFT_deps = utils/DrIFT-src/*hs
GENERATERULES_deps = utils/GenerateRules/*hs $(DRIFT_deps)
INLINEAXIOMS_deps = utils/InlineAxioms/*hs

HC         = ghc
PERL       = perl
HAPPY      = happy
DRIFT      = $(DRIFT_ENV) utils/DrIFT
INLINEAXIOMS = utils/outlineAxioms
HADDOCK    = haddock

HC_FLAGS   = -Wall -fglasgow-exts -cpp  
# -fglasgow-exts comes in via  ../uni/uni-package.conf
# but added it here in case of compilation without uni

HC_INCLUDE = -i$(INCLUDE_PATH)
HC_PACKAGE = -package-conf ../uni/uni-package.conf  -package uni-davinci \
             -package uni-server

### Profiling and Warnings (only for debugging)
### Attention every module must be compiled with profiling or the linker
### cannot link the various .o files properly. So after switching on
### Profiling, do an 'gmake clean; gmake'
### If you need Profiling comment out the following line 
#HC_PROF    = -prof -auto-all 

HCI_OPTS    = $(HC_FLAGS) $(HC_PACKAGE) $(HC_INCLUDE)
HC_OPTS     = $(HCI_OPTS) $(HC_PROF)
DRIFT_OPTS  = +RTS -K10m -RTS

### list of directories to run checks in
TESTDIRS    = Common CASL HasCASL Haskell/Hatchet/examples ToHaskell/test


####################################################################
## sources for hetcats (semi - manually produced with a perl script)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),bin_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),distclean)
ifneq ($(MAKECMDGOALS),genRules)
ifneq ($(MAKECMDGOALS),utils/genRules)
ifneq ($(MAKECMDGOALS),hets-opt)
ifneq ($(MAKECMDGOALS),prob_objs)
ifneq ($(MAKECMDGOALS),hets-optimized)
ifneq ($(MAKECMDGOALS),derivedSources)
ifneq ($(MAKECMDGOALS),$(INLINEAXIOMS))
ifneq ($(MAKECMDGOALS),release)
ifneq ($(MAKECMDGOALS),check)
ifneq ($(MAKECMDGOALS),apache_doc)
ifneq ($(MAKECMDGOALS),clean_genRules)
ifneq ($(MAKECMDGOALS),atctest2)
ifneq ($(MAKECMDGOALS),hetana)
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

drifted_files = Syntax/AS_Architecture.hs Syntax/AS_Library.hs \
    Common/AS_Annotation.hs CASL/AS_Basic_CASL.hs Syntax/AS_Structured.hs \
    Modal/AS_Modal.hs CoCASL/AS_CoCASL.hs COL/AS_COL.hs \
    $(gendrifted_files)

genrule_header_files = $(wildcard ATC/*.header.hs)

genrule_files = Common/Lib/Graph.hs Common/Id.hs Common/Result.hs \
                Common/AS_Annotation.der.hs \
                Syntax/AS_Structured.der.hs Syntax/AS_Architecture.der.hs \
                Common/GlobalAnnotations.hs Syntax/AS_Library.der.hs \
                CASL/Sublogic.hs \
                CASL/Morphism.hs CASL/Sign.hs CASL/AS_Basic_CASL.der.hs \
                HasCASL/As.hs HasCASL/Le.hs HasCASL/Morphism.hs \
                HasCASL/Sublogic.hs \
                Modal/AS_Modal.hs Modal/ModalSign.hs \
                CoCASL/AS_CoCASL.hs CoCASL/CoCASLSign.hs \
                COL/AS_COL.hs COL/COLSign.hs \
                CspCASL/AS_CSP_CASL.hs \
                Static/DevGraph.hs \
                Haskell/Hatchet/AnnotatedHsSyn.hs \
                Haskell/Hatchet/MultiModuleBasics.hs \
                Haskell/Hatchet/HsSyn.hs \
                Haskell/Hatchet/Representation.hs\
                Haskell/Hatchet/Class.hs Haskell/Hatchet/KindInference.hs \
                Haskell/Hatchet/Env.hs \
                Isabelle/IsaSign.hs 

gendrifted_files = ATC/Graph.hs ATC/Id.hs ATC/Result.hs ATC/AS_Annotation.hs \
                   ATC/AS_Library.hs ATC/GlobalAnnotations.hs \
                   ATC/AS_Structured.hs ATC/AS_Architecture.hs \
                   ATC/DevGraph.hs \
                   CASL/ATC_CASL.hs Haskell/ATC_Haskell.hs \
                   HasCASL/ATC_HasCASL.hs CspCASL/ATC_CspCASL.hs \
                   Modal/ATC_Modal.hs CoCASL/ATC_CoCASL.hs COL/ATC_COL.hs \
                   ATC/IsaSign.hs

generated_rule_files = $(patsubst %.hs,%.der.hs,$(gendrifted_files))

inline_axiom_files = Comorphisms/CASL2PCFOL.hs Comorphisms/PCFOL2FOL.hs Comorphisms/Modal2CASL.hs
gen_inline_axiom_files = $(patsubst %.hs,%.inline.hs,$(inline_axiom_files))

happy_files = Haskell/Hatchet/HsParser.hs

# this variable holds the modules that should be documented
# the imported parsec library is not included!
doc_sources = $(filter-out ./Isabelle/IsaSign.hs ,$(sources))

####################################################################
### targets

.PHONY : clean d_clean real_clean bin_clean check hetana hetpa hetdg \
         clean_genRules genRules

.SECONDARY : %.hs %.d $(generated_rule_files) $(gen_inline_axiom_files)
#.PRECIOUS: sources_hetcats.mk

all: hets

hets: $(sources)
	$(HC) --make -o $@ hets.hs $(HC_OPTS) 2>&1 | tee hetcats-make 

hets-opt: hetcats/Version.hs
	$(MAKE) distclean
	$(MAKE) derivedSources
	$(MAKE) real_clean
	$(MAKE) prob_objs
	$(MAKE) hets-optimized

problematic_objs = Common/Lib/Rel.o Common/Id.o Common/Lexer.o Common/Lib/Pretty.o Common/GlobalAnnotations.o Common/PPUtils.o 

ifeq ($(MAKECMDGOALS),prob_objs)
include $(problematic_objs:%.o=%.d)
endif

prob_objs: $(problematic_objs)

hets-optimized:  
	$(HC) --make -O -o hets hets.hs $(HC_OPTS) -w 2>&1 | tee hetcats-make
	strip hets 

hets-old: $(objects)
	$(RM) $@
	$(HC) -o hets $(HC_OPTS) $(objects)

hets.cgi: $(sources) GUI/hets_cgi.hs
	ghc --make -package-conf /home/luettich/ghc-pkg/package.conf -package WASH-CGI GUI/hets_cgi.hs -o hets.cgi $(HC_OPTS)

hetcats-make: hets.hs utils/create_sources.pl $(drifted_files) $(happy_files) $(inline_axiom_files) Modal/ModalSystems.hs
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
### count lines of code
count: $(sources)
	wc -l $(sources)
###############################
### Documentation via haddock
doc: docs/index.html

# index for prelude is missing
docs/index.html: $(doc_sources)
	$(HADDOCK) $(doc_sources) -o docs -h \
          -i docs/base.haddock \
          -t 'hets -- a heterogenous Specification (CASL) tool set'

apache_doc:
	$(RM) docs/*.*
	cvs up -d
	$(MAKE) hets-opt
	$(MAKE) doc
	$(MAKE) post_doc4apache

post_doc4apache:
	$(PERL) utils/post_process_docs.pl docs \
            'Common.Lib.Map.html:Common.Lib._Map.html'
	cp docs/*.* a-docs/

###############################
### release management

derivedSources: $(drifted_files) $(happy_files) hetcats/Version.hs $(inline_axiom_files) Modal/ModalSystems.hs

utils/DrIFT: $(DRIFT_deps)
	(cd utils/DrIFT-src; $(HC) --make DrIFT.hs -o ../DrIFT && \
           strip ../DrIFT)

utils/genRules: $(GENERATERULES_deps)
	(cd utils/GenerateRules; \
         $(HC) --make '-i../..:../DrIFT-src' -package text GenerateRules.hs -o ../genRules && \
         strip ../genRules)

$(INLINEAXIOMS): $(INLINEAXIOMS_deps)
	$(HC) --make utils/InlineAxioms/InlineAxioms.hs \
                          $(HC_OPTS) -o $(INLINEAXIOMS)
	strip $(INLINEAXIOMS)

release: 
	$(RM) -r HetCATS
	cvs -d :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository co HetCATS
	$(RM) -r uni
	ln -s ../uni uni
	(cd HetCATS; $(MAKE) derivedSources; ./clean.sh; \
           find . -name CVS -o -name \*.o -o -name \*.hi | xargs $(RM) -r; \
           $(RM) clean.*; mv Makefile Makefile.orig; \
           mv ReleaseMakefile Makefile)
	tar cvf HetCATS.tar HetCATS

install-hets:
	chmod g+w hets
	cp -p hets $(INSTALLDIR)/versions/hets-`cat version_nr`
	cp -p version_nr $(INSTALLDIR)
	(cd $(INSTALLDIR); $(RM) hets; \
	    ln -s versions/hets-`cat version_nr` hets; $(RM) version_nr)

install: hets-opt install-hets

#############################
### ATC DrIFT-rule generation

genRules: $(generated_rule_files) utils/genRules

$(generated_rule_files): $(genrule_files) utils/genRules #$(genrule_header_files)
	$(MAKE) clean_genRules
	$(foreach file,$(atc_files),$(gen_atc_files))
	utils/genRules -r $(rule) -o CASL $(casl_files)
	utils/genRules -r $(rule) -o HasCASL $(hascasl_files)
	utils/genRules -r $(rule) -o Modal $(modal_files)
	utils/genRules -r $(rule) -o CoCASL $(cocasl_files)
	utils/genRules -r $(rule) -o COL $(col_files)
	utils/genRules -r $(rule) -o CspCASL $(cspcasl_files)
	utils/genRules -r $(rule) -o Haskell -h ATC/Haskell.header.hs \
            $(haskell_files)

rule = ShATermConvertible

gen_atc_files = if [ -f ATC/$(basename $(basename $(notdir $(file)))).header.hs ]; then \
                   utils/genRules -r $(rule) -o ATC -h ATC/$(basename $(basename $(notdir $(file)))).header.hs $(file); \
                else \
                   utils/genRules -r $(rule) -o ATC $(file); \
                fi ;

atc_files := $(filter-out CASL/% HasCASL/% Modal/% CoCASL/% COL/% CspCASL/% Haskell/% ,$(genrule_files))
casl_files := $(filter CASL/% ,$(genrule_files))
hascasl_files := $(filter HasCASL/% ,$(genrule_files))
modal_files := $(filter Modal/% ,$(genrule_files))
cocasl_files := $(filter CoCASL/% ,$(genrule_files))
col_files := $(filter COL/% ,$(genrule_files))
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
	$(RM) atctest2
	$(RM) atctest
	$(RM) Common/annos

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
	$(RM) $(drifted_file) $(inline_axiom_files)
	$(RM) utils/DrIFT utils/genRules $(INLINEAXIOMS)
#	$(RM) $(happy_files)

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

CASL/capa: CASL/capa.hs Common/*.hs CASL/*.hs
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### HasCASL parser
hacapa: HasCASL/hacapa

HasCASL/hacapa: HasCASL/hacapa.hs Common/*.hs HasCASL/*.hs 
	$(RM) $@
	$(HC) --make -o $@ $< $(HC_OPTS)

### Haskell parser
hapa: Haskell/hapa

Haskell/hapa: Haskell/hapa.hs Haskell/Hatchet/*.hs $(happy_files)
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

atctest2: Common/ATerm/ATermLibTest.hs Common/SimpPretty.hs Common/ATerm/*.hs Common/Lib/*.hs
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

%.hs: %.der.hs utils/DrIFT
	$(DRIFT) $(DRIFT_OPTS) $< > $@

## rules for inlineAxioms
%.hs: %.inline.hs $(INLINEAXIOMS)
	$(INLINEAXIOMS) $< > $@

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

## rule for Modal/ModalSystems.hs needed for ModalLogic Translation
Modal/ModalSystems.hs: Modal/GeneratePatterns.inline.hs.in utils/genTransMFormFunc.pl $(INLINEAXIOMS)
	$(PERL) utils/genTransMFormFunc.pl $< $@


####################################################################
## Setting a global search path (for dependency files)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),d_clean)
ifneq ($(MAKECMDGOALS),real_clean)
ifneq ($(MAKECMDGOALS),distclean)
ifneq ($(MAKECMDGOALS),genRules)
ifneq ($(MAKECMDGOALS),utils/genRules)
ifneq ($(MAKECMDGOALS),derivedSources)
ifneq ($(MAKECMDGOALS),release)
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
endif
endif
endif
