# Makefile
# $Id$
# Author: (c) Klaus Lüttich, Christian Maeder, Uni Bremen 2002-2005
# Year:   2004

# This Makefile will compile the new hets system and provides also
# targets for test programs during implementation phases.

# !!! Note: This makefile is written for GNU make !!!
#           (gmake on solaris)

all: hets

####################################################################
## Some varibles, which control the compilation

INCLUDE_PATH =
HAIFA_PATHS = Network Network/Server Org Org/W3 Org/W3/N2001 \
    Org/Xmlsoap Org/Xmlsoap/Schemas Org/Xmlsoap/Schemas/Soap \
    Text Text/XML Text/XML/HXT Text/XML/Schema Text/XML/Schema/TypeMapper \
    Text/XML/Serializer

SOURCE_PATHS = . utils/itcor \
    utils utils/DrIFT-src utils/GenerateRules utils/InlineAxioms Common \
    Common/Lib Common/ATerm Logic CASL CASL/CCC CASL/CompositionTable \
    Syntax Static GUI HasCASL Haskell Modal CoCASL COL ConstraintCASL \
    CspCASL ATC Proofs Comorphisms Isabelle Driver \
    Taxonomy CASL_DL SoftFOL OWL_DL OMDoc PGIP Propositional

# the 'replacing spaces' example was taken from the (GNU) Make info manual
empty =
space = $(empty) $(empty)

## set ghc imports properly for your system
GHC_IMPORTS = `$(HC) --print-libdir`/imports
# import directories for ghc-5.04.2
GHC5 = $(GHC_IMPORTS)/base:$(GHC_IMPORTS)/haskell98
DRIFT_ENV = \
    DERIVEPATH=.:$(GHC_IMPORTS):$(GHC5):$(subst $(space),:,$(PFE_PATHS))

# override on commandline for other architectures
INSTALLDIR = \
    /home/www/agbkb/forschung/formal_methods/CoFI/hets/`utils/sysname.sh`

DRIFT_deps = utils/DrIFT-src/*hs
GENERATERULES_deps = utils/GenerateRules/*hs $(DRIFT_deps)
GENITCORRECTIONS_deps = utils/itcor/GenItCorrections.hs
INLINEAXIOMS_deps = utils/InlineAxioms/InlineAxioms.hs \
    Common/Doc.hs CASL/ToDoc.hs Modal/AS_Modal.hs \
    Modal/Parse_AS.hs Modal/ModalSign.hs Modal/Print_AS.hs Modal/StatAna.hs

HC = ghc
HCPKG = ghc-pkg
PERL = perl
HAPPY = happy -sga
GENRULES = utils/genRules
GENRULECALL = $(GENRULES) -r Typeable -r ShATermConvertible \
    -i Data.Typeable -i Common.ATerm.Lib
DRIFT = utils/DrIFT
INLINEAXIOMS = utils/outlineAxioms
HADDOCK = haddock

OSBYUNAME = $(shell uname)
ifneq ($(findstring SunOS, $(OSBYUNAME)),)
TAR = gtar
else
TAR = tar
endif

ARCH = $(subst $(space),,$(shell uname -m))
SETUP = utils/Setup
SETUPPREFIX = --prefix=$(HOME)/.ghc/$(ARCH)-$(OSBYUNAME)-hets-packages

SETUPPACKAGE = ../$(SETUP) clean; \
    ../$(SETUP) configure -p $(SETUPPREFIX); \
    ../$(SETUP) build; ../$(SETUP) haddock; ../$(SETUP) install --user

HAXMLVERSION = $(shell $(HCPKG) field HaXml version)
ifneq ($(findstring 1.13.2, $(HAXMLVERSION)),)
HAXML_PACKAGE = -package HaXml -DHAXML_PACKAGE
endif

# remove -fno-warn-orphans for older ghcs and add -ifgl
HC_WARN = -Wall -fno-warn-orphans
HC_FLAGS = $(HAXML_PACKAGE) \
    $(HC_WARN) -fglasgow-exts -fallow-overlapping-instances \
# -ddump-minimal-imports
# uncomment to above line to generate .imports files for displayDependencyGraph


HC_OPTS_MAC := $(if $(findstring Darwin,$(shell uname -s)), \
    -optl-F$(HOME)/Library/Frameworks -optl-framework -optlGNUreadline,)

HC_INCLUDE = $(addprefix -i, $(INCLUDE_PATH))

logics = CASL HasCASL Isabelle Modal CoCASL COL CspCASL CASL_DL SoftFOL \
    OWL_DL ConstraintCASL Propositional

TESTTARGETFILES += CASL/fromKif.hs CASL/capa.hs HasCASL/hacapa.hs \
    Haskell/wrap.hs Isabelle/isa.hs Syntax/hetpa.hs \
    ATC/ATCTest.hs ATC/ATCTest2.hs Common/ATerm/ATermLibTest.hs \
    Common/ATerm/ATermDiffMain.hs Common/annos.hs Common/test_parser.hs \
    SoftFOL/tests/PrintTPTPTests.hs Comorphisms/test/showKP.hs \
    SoftFOL/tests/soapTest.hs Comorphisms/test/sublogicGraph.hs

UNI_PACKAGE_CONF = $(wildcard ../uni/uni-package.conf)
ifneq ($(strip $(UNI_PACKAGE_CONF)),)
HC_PACKAGE = -package-conf $(UNI_PACKAGE_CONF) -package uni-davinci \
    -package uni-server -DUNI_PACKAGE

# some modules from uni for haddock
# if uni/server is included also HaXml sources are needed
uni_dirs = ../uni/davinci ../uni/graphs ../uni/events \
    ../uni/reactor ../uni/util ../uni/posixutil

uni_sources = $(wildcard $(addsuffix /haddock/*.hs, $(uni_dirs))) \
    $(wildcard ../uni/htk/haddock/*/*.hs)
TESTTARGETFILES += OWL_DL/ToHaskellAS.hs Taxonomy/taxonomyTool.hs \
    SoftFOL/tests/CMDL_tests.hs Static/test/TestDGTrans.hs
endif

### list of directories to run checks in
TESTDIRS += Common CASL HasCASL test

hs_clean_files = Haskell/TiATC.hs Haskell/TiDecorateATC.hs \
    Haskell/TiPropATC.hs Haskell/ATC_Haskell.der.hs

PFE_TOOLDIR = $(wildcard ../programatica/tools)
ifneq ($(strip $(PFE_TOOLDIR)),)
PFE_DIRS = base/AST base/TI base/parse2 base/parse2/Lexer base/parse2/Parser \
    base/parse2/LexerGen base/parse2/LexerSpec base/tests/HbcLibraries \
    base/pretty base/syntax base/lib base/lib/Monads base/Modules base/defs \
    base/transforms base/transforms/Deriving property \
    property/syntax property/AST property/transforms \
    property/TI property/defs property/parse2 property/parse2/Parser

PFE_PATHS = $(addprefix $(PFE_TOOLDIR)/, $(PFE_DIRS))
pfe_sources = $(wildcard $(addsuffix /*hs, $(PFE_PATHS)))
PFE_PATH = $(addprefix -i, $(PFE_PATHS))
PFE_FLAGS = -package programatica -DPROGRAMATICA
happy_files += $(PFE_TOOLDIR)/property/parse2/Parser/PropParser.hs

LEX_DIR = $(PFE_TOOLDIR)/base/parse2/Lexer

programatica_pkg: $(PFE_TOOLDIR)/property/parse2/Parser/PropParser.hs \
            $(LEX_DIR)/HsLex.hs $(SETUP)
	@if $(HCPKG) field programatica version; then \
          echo "of programatica package found"; else \
          (patch -usNlp0 -d $(PFE_TOOLDIR) \
            -i `pwd`/Haskell/Programatica.patch || exit 0); \
          cp -f utils/programatica.cabal ../programatica/tools; \
          cp -f $(SETUP) ../programatica/tools; \
          (cd ../programatica/tools; \
           ./Setup configure $(SETUPPREFIX); \
           ./Setup build; ./Setup install --user) fi

$(LEX_DIR)/HsLex.hs: $(LEX_DIR)Gen/HsLexerGen
	echo "{-# OPTIONS -w #-}" > $@
	$< >> $@

$(LEX_DIR)Gen/HsLexerGen: $(LEX_DIR)Gen/*.hs $(LEX_DIR)Spec/*.hs \
    $(LEX_DIR)/HsTokens.hs
	$(HC) --make -fno-monomorphism-restriction -O \
           -i$(PFE_TOOLDIR)/base/tests/HbcLibraries \
           -i$(PFE_TOOLDIR)/base/lib \
	   -i$(LEX_DIR) -i$(LEX_DIR)Gen -i$(LEX_DIR)Spec \
              $@.hs -o $@
	strip $@

logics += Haskell
derived_sources += Haskell/PreludeString.hs $(LEX_DIR)/HsLex.hs \
    $(LEX_DIR)Gen/HsLexerGen

utils/appendHaskellPreludeString: utils/appendHaskellPreludeString.hs
	$(HC) --make -o $@ $<

APPENDPRELUDESTRING = utils/appendHaskellPreludeString \
    Haskell/ProgramaticaPrelude.hs

## rule for appendHaskellPreludeString
Haskell/PreludeString.hs: Haskell/PreludeString.append.hs \
    $(APPENDPRELUDESTRING)
	$(RM) $@
	$(APPENDPRELUDESTRING) < $< > $@
	chmod 444 $@

Ast_Haskell_files = HsDeclStruct HsExpStruct HsFieldsStruct \
    HsGuardsStruct HsKindStruct HsPatStruct HsTypeStruct HsAssocStruct \
    HsModule HsName HsLiteral HsIdent

#files in base/TI/
#Ti_Haskell_files = TiTypes TiKinds TiDecorate TiInstanceDB

#Ti_Prop_files = property/TI/TiPropDecorate property/syntax/PropSyntaxRec

Other_PFE_files = property/AST/HsPropStruct base/defs/PNT \
    base/defs/UniqueNames base/Modules/TypedIds base/Modules/Ents \
    base/parse2/SourceNames base/syntax/SyntaxRec \
    property/syntax/PropSyntaxStruct

Haskell_files = $(addsuffix .hs, \
    $(addprefix $(PFE_TOOLDIR)/base/AST/, $(Ast_Haskell_files)) \
    $(addprefix $(PFE_TOOLDIR)/, $(Other_PFE_files)))

## rule for ATC generation
Haskell/ATC_Haskell.der.hs: $(Haskell_files) $(GENRULES)
	$(GENRULECALL) -i Haskell.BaseATC -o $@ $(Haskell_files)

hs_der_files += $(hs_clean_files)

TESTDIRS += ToHaskell Haskell/test
TESTTARGETFILES += Haskell/hana.hs Haskell/h2h.hs Haskell/h2hf.hs
endif

TESTTARGETS = Test.o $(subst .hs,,$(TESTTARGETFILES))

### Profiling (only for debugging)
### Attention every module must be compiled with profiling or the linker
### cannot link the various .o files properly. So after switching on
### Profiling, do an 'gmake real_clean; gmake'
### Comment in the following line for switching on profiling.
#HC_PROF = -prof -auto-all -fignore-asserts

HC_OPTS = $(HC_FLAGS) $(HC_INCLUDE) $(HC_PACKAGE) $(PFE_FLAGS) $(HC_PROF) \
   -DCASLEXTENSIONS $(HC_OPTS_MAC)

####################################################################
## sources for hets

non_sources = Common/LaTeX_maps.svmono.hs Common/CaslLanguage.hs ./Test.hs \
    $(SETUP).hs

sources = hets.hs $(filter-out $(non_sources), \
    $(wildcard $(addsuffix /[A-Z]*hs, $(SOURCE_PATHS))))

objects = $(sources:%.hs=%.o)

drifted_files = Syntax/AS_Architecture.hs Syntax/AS_Library.hs \
    Common/AS_Annotation.hs CASL/AS_Basic_CASL.hs Syntax/AS_Structured.hs \
    ATC/DevGraph.hs \
    Modal/AS_Modal.hs CoCASL/AS_CoCASL.hs COL/AS_COL.hs CASL_DL/AS_CASL_DL.hs\
    ConstraintCASL/AS_ConstraintCASL.hs\
    Propositional/AS_BASIC_Propositional.hs\
    $(gendrifted_files)

atc_files = Common/AS_Annotation.der.hs Common/DefaultMorphism.hs \
    Syntax/AS_Structured.der.hs Syntax/AS_Architecture.der.hs \
    Common/GlobalAnnotations.hs Syntax/AS_Library.der.hs \
    Logic/Prover.hs #Common/Id.hs Common/Result.hs OWL_DL/AS.hs

atc_der_files = $(foreach file, $(atc_files), \
    ATC/$(basename $(basename $(notdir $(file)))).der.hs)

ATC/Id.der.hs: Common/Id.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/Result.der.hs: Common/Result.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/AS_Annotation.der.hs: Common/AS_Annotation.der.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/DefaultMorphism.der.hs: Common/DefaultMorphism.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/AS_Structured.der.hs: Syntax/AS_Structured.der.hs $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -i ATC.Grothendieck -o $@ $<

ATC/AS_Architecture.der.hs: Syntax/AS_Architecture.der.hs $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Structured -o $@ $<

ATC/AS_Library.der.hs: Syntax/AS_Library.der.hs $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Architecture -o $@ $<

ATC/GlobalAnnotations.der.hs: Common/GlobalAnnotations.hs $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $<

ATC/Prover.der.hs: Logic/Prover.hs $(GENRULES)
	$(GENRULECALL) -x Logic.Prover.ProverTemplate \
            -i ATC.AS_Annotation -o $@ $<

ATC/DevGraph.der.hs: Static/DevGraph.hs $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Library -i ATC.Grothendieck -o $@ $<

CASL_files = CASL/Sublogic.hs CASL/Morphism.hs CASL/Sign.hs \
    CASL/AS_Basic_CASL.der.hs

HasCASL_files = Common/Prec.hs HasCASL/As.hs HasCASL/Le.hs HasCASL/Sublogic.hs

Isabelle_files = Isabelle/IsaSign.hs

Propositional_files = Propositional/Sign.hs Propositional/Morphism.hs \
            Propositional/AS_BASIC_Propositional.hs Propositional/Symbol.hs\
            Propositional/Sublogic.hs
Modal_files = Modal/AS_Modal.hs Modal/ModalSign.hs
ConstraintCASL_files = ConstraintCASL/AS_ConstraintCASL.hs
CoCASL_files = CoCASL/AS_CoCASL.hs CoCASL/CoCASLSign.hs
COL_files = COL/AS_COL.hs COL/COLSign.hs
CspCASL_files = CspCASL/AS_CspCASL.hs CspCASL/AS_CspCASL_Process.hs \
             CspCASL/SignCSP.hs

CASL_DL_files = CASL_DL/AS_CASL_DL.hs CASL_DL/Sign.hs

SoftFOL_files = SoftFOL/Sign.hs

OWL_DL_files = OWL_DL/Sign.hs

atc_logic_files = $(foreach logic, $(logics), $(logic)/ATC_$(logic).der.hs)

generated_rule_files = $(atc_der_files) $(atc_logic_files)

gendrifted_files = $(patsubst %.der.hs, %.hs, $(generated_rule_files))

inline_axiom_files = Comorphisms/CASL2PCFOL.hs \
    Comorphisms/Modal2CASL.hs Comorphisms/CASL2TopSort.hs \
    Comorphisms/CASL2SubCFOL.hs CASL_DL/PredefinedSign.hs

gen_inline_axiom_files = $(patsubst %.hs,%.inline.hs, $(inline_axiom_files))

derived_sources += $(drifted_files) Driver/Version.hs $(happy_files) \
    $(inline_axiom_files) Modal/ModalSystems.hs $(hs_der_files) \
    OWL_DL/ReadWrite.hs ConstraintCASL/AS_ConstraintCASL.hs

# sources that have {-# OPTIONS -cpp #-}
cpp_sources = \
    Isabelle/CreateTheories.hs \
    SoftFOL/Logic_SoftFOL.hs GUI/Utils.hs Driver/WriteFn.hs \
    Propositional/Logic_Propositional.hs \
    Comorphisms/LogicList.hs Comorphisms/LogicGraph.hs \
    Comorphisms/KnownProvers.hs hets.hs $(happy_files) \
    PGIP/InfoCommands.hs PGIP/ProveCommands.hs

# unused, remove when header files are gone
genrule_header_files = $(wildcard ATC/*.header.hs)

nondoc_sources = $(wildcard utils/DrIFT-src/*.hs) \
    $(wildcard utils/DrIFT-src/*.lhs) \
    $(wildcard utils/GenerateRules/*.hs) \
    $(wildcard utils/InlineAxioms/*.hs) \
    $(cpp_sources) $(pfe_sources) $(gen_inline_axiom_files) \
    $(genrule_header_files) $(generated_rule_files) \
    $(PFE_TOOLDIR)/property/parse2/Parser/PropParser.hspp \
    Modal/GeneratePatterns.inline.hs \
    Haskell/PreludeString.append.hs Haskell/ProgramaticaPrelude.hs \
    SoftFOL/MathServCommunication.hs \
    $(patsubst %.hs, %.der.hs, $(drifted_files))

hspp_sources = $(patsubst %.hs, %.hspp, $(cpp_sources))

# this variable holds the modules that should be documented
doc_sources = $(filter-out $(nondoc_sources), $(sources) $(hspp_sources))

tax_sources = Taxonomy/AbstractGraphView.hs Taxonomy/MMiSSOntology.hs \
    Taxonomy/MMiSSOntologyGraph.hs Taxonomy/OntoParser.hs

tax_objects = $(patsubst %.hs, %.o, $(tax_sources))

####################################################################
### targets

.PHONY : all hets-opt hets-optimized clean o_clean clean_pretty \
    real_clean bin_clean package_clean distclean packages \
    http_pkg syb_pkg shellac_pkg shread_pkg hxt_pkg haifa_pkg \
    check capa hacapa h2h h2hf showKP clean_genRules genRules \
    count doc apache_doc post_doc4apache fromKif \
    programatica_pkg maintainer-clean annos \
    derivedSources install_hets install release cgi ghci

.SECONDARY : %.hs %.d $(generated_rule_files) $(gen_inline_axiom_files)

$(SETUP): utils/Setup.hs
	$(HC) --make -O -o $@ $<

packages: http_pkg syb_pkg shellac_pkg shread_pkg hxt_pkg haifa_pkg \
  programatica_pkg

http_pkg: utils/http.tgz $(SETUP)
	@if $(HCPKG) field HTTP version; then \
          echo "of HTTP package found"; else \
          $(RM) -r http; \
          $(TAR) zxf utils/http.tgz; \
          (cd http; $(SETUPPACKAGE)) fi

syb_pkg: $(SETUP)
	@if $(HCPKG) field syb-generics version; then \
          echo "of syb-generics package found"; else \
          (cd syb-generics; $(SETUPPACKAGE)) fi

shellac_pkg: utils/shellac.tgz $(SETUP)
	@if $(HCPKG) field Shellac version; then \
          echo "of shellac package found"; else \
          $(RM) -r shellac; \
          $(TAR) zxf utils/shellac.tgz; \
          (cd shellac; $(SETUPPACKAGE)) fi

shread_pkg: utils/shread.tgz $(SETUP) shellac_pkg
	@if $(HCPKG) field Shellac-readline version; then \
          echo "of shellac-readline package found"; else \
          $(RM) -rf shread; \
          $(TAR) zxf utils/shread.tgz; \
          (cd shread; $(SETUPPACKAGE)) fi

hxt_pkg: $(SETUP) http_pkg
	@if $(HCPKG) field hxt version; then \
          echo "of hxt package found"; else \
          $(RM) -rf hxt; \
          $(TAR) zxf utils/hxt.tgz; \
          (cd hxt; $(SETUPPACKAGE)) fi

haifa_pkg: $(SETUP) hxt_pkg syb_pkg
	@if $(HCPKG) field HAIFA version; then \
          echo "of HAIFA package found"; else \
          (cd haifa-lite; $(SETUPPACKAGE)) fi

programatica_pkg:

hets-opt:
	$(MAKE) distclean
	$(MAKE) derivedSources
	$(MAKE) clean
	$(MAKE) hets-optimized

hets-optimized: $(derived_sources)
	$(HC) --make -O -o hets hets.hs $(HC_OPTS)
	strip hets

hets-old: $(objects)
	$(RM) $@
	$(HC) -o hets $(HC_OPTS) $(objects)

cgi:
	$(MAKE) distclean
	$(MAKE) derivedSources
	$(MAKE) real_clean
	$(MAKE) hets.cgi

hets.cgi: $(sources) GUI/hets_cgi.hs
	ghc --make GUI/hets_cgi.hs -o $@ $(HC_OPTS) -O
	strip hets.cgi

hets_maintainers.txt: $(sources)
	@echo 'File : Maintainer' > $@
	@echo -n Generating $@ " "
	@egrep -m 1 "Maintainer" $(sources) | \
          sed -e 's/: *Maintainer *: */ : /' >> $@
	@echo " done"

###############################
### count lines of code
count: $(sources)
	wc -l $(sources)
###############################
### Documentation via haddock
doc: docs/index.html

# generate haddock documentation with links to sources
# the interface treatment is stolen from uni/mk/suffix.mk
docs/index.html: $(doc_sources)
	$(RM) -r docs
	mkdir docs
	cp -r -L ../uni/www docs/www || mkdir docs/www
	HINTERFACES0=`find -L docs/www -name '*.haddock' \
           -printf "--read-interface=www/%P,%p "` ; \
        HINTERFACES=`echo $$HINTERFACES0 | \
           $(PERL) -pe 's+/[^/]*.haddock,+,+g'` ; \
        $(HADDOCK) -o docs -h -v -s ../%F $$HINTERFACES \
            -t 'Hets - the Heterogeneous Tool Set' \
            -p Hets-Haddock-Prologue.txt $(doc_sources)

# sources are not copied here
apache_doc:
	$(RM) -r docs
	cvs up -d ; echo "CVS exited with: " $$?
	$(MAKE) hets-opt
	$(MAKE) doc
	$(MAKE) post_doc4apache
	$(MAKE) o_clean
	$(MAKE) hets.cgi

post_doc4apache:
	$(RM) -r a-docs
	cp -r docs a-docs
	$(PERL) utils/post_process_docs.pl a-docs \
            'Common.Lib.Map.html:Common.Lib._Map.html'
	$(PERL) utils/post_process_docs.pl a-docs \
            'Data.Map.html:Data._Map.html'

###############################
### release management

derivedSources: $(derived_sources) $(hspp_sources)

utils/DrIFT: $(DRIFT_deps)
	(cd utils/DrIFT-src; $(HC) --make DrIFT.hs -o ../DrIFT && \
            strip ../DrIFT)

utils/genRules: $(GENERATERULES_deps)
	(cd utils/GenerateRules; \
            $(HC) --make -i../DrIFT-src -i../.. $(HC_WARN) \
                GenerateRules.hs -o ../genRules && strip ../genRules)

# "-package hssource" for ghc-5.04.2
$(INLINEAXIOMS): $(INLINEAXIOMS_deps)
	$(HC) --make utils/InlineAxioms/InlineAxioms.hs $(HC_WARN) $(HC_PROF) \
            -i../.. -o $(INLINEAXIOMS)
	strip $(INLINEAXIOMS)

REV = trunk
release:
	$(RM) -r Hets
	svn co https://svn-agbkb.informatik.uni-bremen.de/Hets/$(REV) Hets
	$(RM) -r uni
	if [ -d ../uni ] ; then ln -s ../uni uni ; fi
	$(RM) -r programatica
	if [ -d ../programatica ] ; then \
            mkdir programatica; \
            ln -s ../../programatica/tools programatica/tools ; fi
	(cd Hets; $(MAKE) derivedSources; $(MAKE) clean; \
            cp Makefile Makefile.orig; \
            cp ReleaseMakefile Makefile; \
            ./clean.sh; \
            find . -name .svn -o -name \*.o -o -name \*.hi | xargs $(RM) -r; \
            $(RM) clean.*; utils/replaceAllHeaders.sh)
	$(TAR) cvf Hets.tar Hets

install-hets:
	chmod g+w hets
	cp -p hets $(INSTALLDIR)/versions/hets-`cat version_nr`
	cp -p version_nr $(INSTALLDIR)
	(cd $(INSTALLDIR); $(RM) hets; \
	    ln -s versions/hets-`cat version_nr` hets; $(RM) version_nr)

install: hets-opt install-hets

pack/install-%.jar: pack/install-%.xml pack/UserInputSpec-%.xml hets.in hets
       ## TODO: add more dependencies and use hets-opt
	compile $< -b . -k standard -o $@
#	compile $< -b . -k web -o $@

###################################
### Common/LaTeX_maps.hs generation

utils/genItCorrections: $(GENITCORRECTIONS_deps)
	$(HC) --make -o $@ $<
	strip $@

pretty/LaTeX_maps.hs: utils/words.pl utils/genItCorrections \
    pretty/words.input pretty/fonts.input pretty/width-table.tex.templ
	@echo -n "Generating pretty/LaTeX_maps.hs ... "
	@(cd pretty >/dev/null; $(PERL) ../utils/words.pl > words.pl.log)
	@(cd pretty >/dev/null; ../utils/genItCorrections \
            gen_it_characters gen_it_words >> LaTeX_maps.hs)
	@echo "ready"
	@echo "please copy the file manually to Common"

#############################
### ATC DrIFT-rule generation

genRules: $(generated_rule_files)

CASL/ATC_CASL.der.hs: $(CASL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ $(CASL_files)

Propositional/ATC_Propositional.der.hs: $(Propositional_files) \
       $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ \
       $(Propositional_files)

HasCASL/ATC_HasCASL.der.hs: $(HasCASL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ $(HasCASL_files)

Isabelle/ATC_Isabelle.der.hs: $(Isabelle_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(Isabelle_files)

Modal/ATC_Modal.der.hs: $(Modal_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(Modal_files)

ConstraintCASL/ATC_ConstraintCASL.der.hs: $(ConstraintCASL_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(ConstraintCASL_files)

CASL_DL/ATC_CASL_DL.der.hs: $(CASL_DL_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(CASL_DL_files)

CoCASL/ATC_CoCASL.der.hs: $(CoCASL_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(CoCASL_files)

COL/ATC_COL.der.hs: $(COL_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(COL_files)

CspCASL/ATC_CspCASL.der.hs: $(CspCASL_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(CspCASL_files)

SoftFOL/ATC_SoftFOL.der.hs: $(SoftFOL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(SoftFOL_files)

OWL_DL/ATC_OWL_DL.der.hs: $(OWL_DL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -i OWL_DL.ReadWrite \
          -o $@ $(OWL_DL_files)

clean_genRules:
	$(RM) $(generated_rule_files) $(gendrifted_files) $(hspp_sources) \
            $(hs_clean_files)

###############
### clean up

clean: bin_clean o_clean clean_pretty

### removes *.hi and *.o in all include directories
o_clean:
	find . -name \*.o -o -name \*.hi | xargs $(RM) -r

### remove binaries
bin_clean:
	$(RM) hets
	$(RM) hets.cgi
	$(RM) $(TESTTARGETS)

clean_pretty:
	$(RM) pretty/*.c.* pretty/*.h.* pretty/gen_it_* \
               pretty/generated_words.tex

### additionally removes the library files
real_clean: clean

### clean user packages
package_clean:
	$(HCPKG) unregister HAIFA --user || exit 0
	$(HCPKG) unregister programatica --user || exit 0
	$(HCPKG) unregister hxt --user || exit 0
	$(HCPKG) unregister Shellac-readline --user || exit 0
	$(HCPKG) unregister HTTP --user || exit 0
	$(HCPKG) unregister syb-generics --user || exit 0
	$(HCPKG) unregister Shellac --user || exit 0

### additionally removes generated files not in the CVS tree
distclean: clean clean_genRules
	$(RM) $(derived_sources)
	$(RM) Modal/GeneratePatterns.inline.hs utils/appendHaskellPreludeString
	$(RM) utils/DrIFT utils/genRules $(INLINEAXIOMS)
	$(RM) utils/genItCorrections pretty/LaTeX_maps.hs pretty/words.pl.log

maintainer-clean: distclean package_clean
	$(RM) $(SETUP)
	$(RM) -r $(HOME)/.ghc/$(ARCH)-$(OSBYUNAME)-hets-packages

####################################################################
### test targets
####################################################################

### interactive
ghci: $(derived_sources)
	$(HC)i $(HC_OPTS)

### christian's target
### CASL parser
fromKif: CASL/fromKif

### Annos parser
annos: Common/annos

### CASL parser
capa: CASL/capa

### HasCASL parser
hacapa: HasCASL/hacapa

### Haskell analysis
hana: Haskell/hana

### Haskell to Isabelle-HOLCF translation
h2hf: Haskell/h2hf

Haskell/h2hf: Haskell/h2hf.hs Haskell/*.hs Isabelle/*.hs Common/*.hs \
    Common/Lib/*.hs Comorphisms/*.hs
	$(HC) -O --make -o $@ $< $(HC_FLAGS) $(PFE_FLAGS)

### HasCASL to Haskell translation
h2h: Haskell/h2h

### test program to check the known provers
showKP: Comorphisms/test/showKP

### run tests in other directories
check: $(TESTTARGETS)
	for i in $(TESTDIRS); do $(MAKE) -C $$i check; done

####################################################################
## Preparing the version of Hets
Driver/Version.hs: Driver/Version.in version_nr
	$(RM) $@
	LANG=C $(PERL) utils/build_version.pl version_nr \
            < Driver/Version.in > $@
	chmod 444 $@

## two hardcoded dependencies for a correct generation of Version.hs
Driver/Options.hs Driver/WriteFn.hs Driver/ReadFn.hs: Driver/Version.hs
hets.hs: Driver/Version.hs

ATC/DevGraph.hs: Static/DevGraph.hs

## two dependencies for avoidence of circular prerequisites
CASL_DEPENDENT_BINARIES= hets CASL/capa CASL/fromKif \
   Common/annos Common/test_parser Comorphisms/test/showKP \
   CspCASL/print_csp HasCASL/hacapa Haskell/h2h Haskell/h2hf \
   Haskell/hana Haskell/wrap Isabelle/isa Syntax/hetpa
$(CASL_DEPENDENT_BINARIES): $(sources) $(derived_sources)
# CASL_DL/Logic.hs: CASL_DL/PredefinedSign.hs
####################################################################
## rules for DrIFT
.SUFFIXES:

%: %.hs packages
	$(HC) --make -o $@ $< $(HC_OPTS)

%.hs: %.y
	$(HAPPY) -o $@.tmp $<
	echo "{-# OPTIONS -w #-}" > $@
	cat $@.tmp >> $@
	$(RM) $@.tmp

%.hs: %.der.hs $(DRIFT)
	$(RM) $@
	($(DRIFT_ENV); export DERIVEPATH; $(DRIFT) $< > $@)
	chmod 444 $@

## rules for inlineAxioms
%.hs: %.inline.hs $(INLINEAXIOMS)
	$(RM) $@
	$(INLINEAXIOMS) $< > $@
	chmod 444 $@

## rule for cpp and haddock
%.hspp: %.hs
	$(HC) -E -cpp -D__HADDOCK__ \
            -DUNI_PACKAGE -DCASLEXTENSIONS -DPROGRAMATICA -optP -P $<

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

## generate the inline file for the predefined CASL_DL sign
CASL_DL/PredefinedSign.inline.hs:  \
     CASL_DL/PredefinedSign.inline.hs.in utils/appendHaskellPreludeString \
     CASL_DL/PredDatatypes.het
	$(RM) $@
	utils/appendHaskellPreludeString CASL_DL/PredDatatypes.het \
          < CASL_DL/PredefinedSign.inline.hs.in > $@
	echo "  )" >> $@
	chmod 444 $@

# Warning: Don't change the order of the depencies!!
CASL_DL/PredDatatypes.het: utils/transformLibAsBasicSpec.pl \
     CASL_DL/Datatypes.het
	$(RM) $@
	$(PERL) $+ > $@
	chmod 444 $@

## rule for Modal/ModalSystems.hs needed for ModalLogic Translation
# uses intransparently utils/outlineAxioms
Modal/ModalSystems.hs: Modal/GeneratePatterns.inline.hs.in \
    utils/genTransMFormFunc.pl $(INLINEAXIOMS)
	$(RM) $@
	$(PERL) utils/genTransMFormFunc.pl $< $@
	chmod 444 $@

initialize_installer:
	@if [ -d $(INSTALLER_DIR) ] ; then   \
	    echo "copy file to $(INSTALLER_DIR)" ; \
	  else \
	    echo "create $(INSTALLER_DIR)"  ;\
	    mkdir -p $(INSTALLER_DIR) ; \
	 fi
	@sed "s/^\(HETS_VERSION=\).*/\1`cat version_nr`/" Makefile.installer > Makefile.inst  ;\
	 sed "s/^\(SPASS_DIR_MAC=\).*/\1`ls utils/SPASS-ppc-mac/ | grep SPASS`/"  Makefile.inst > Makefile.inst2 ;\
	 rm Makefile.inst ;\
	 mv Makefile.inst2 $(INSTALLER_DIR)/Makefile  ;\
	 cp utils/getAllHets.sh $(INSTALLER_DIR)/
	@echo =========================================================================
	@echo If you have not logged in \'cvs.haskell.org\' and \'cvs-agbkb.informatik.uni-bremen.de\'
	@echo "then please first login:"
	@echo  "   cvs -d :pserver:anoncvs@cvs.haskell.org:/cvs login"
	@echo  "    the password is cvs"
	@echo  "   cvs -d :pserver:cvsread@cvs-agbkb.informatik.uni-bremen.de:/repository login "
	@echo  "    the password is "
	@echo =========================================================================
	@echo Ready to create installers for Hets
	@echo Please do
	@echo "  -> cd $(INSTALLER_DIR)"
	@echo "  -> make"
	@echo and wait until it is finished






