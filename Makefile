#!/usr/bin/make -f

# Makefile
#
# Authors: (c) Klaus Luettich, Christian Maeder, Uni Bremen 2002-2009
#              Jens Elkner, Uni Magdeburg 2016

# This GNU Makefile will compile the hets system and provides also
# targets for test programs during implementation phases.
#
# If the following environment variables are set, their values get passed to
# the corresponding tool as is: GHC_PKG_FLAGS (ghc-pkg), GHC_FLAGS (ghc).

include var.mk

NO_BIND_WARNING := -fno-warn-unused-do-bind
HC_WARN := -Wall -fwarn-tabs \
  -fwarn-unrecognised-pragmas -fno-warn-orphans $(NO_BIND_WARNING)
# uncomment HC_PROF for profiling (and comment out packages in var.mk)
# call resulting binary with a final +RTS -p to get a file <binary>.prof
#HC_PROF := -prof -auto-all -osuf p_o +RTS -K100m -RTS
HC_OPTS += $(HC_WARN) $(HC_PROF) $(GHC_FLAGS)
# -ddump-minimal-imports
# uncomment the above line to generate .imports files for displayDependencyGraph

.DEFAULT_GOAL := hets

.NOTPARALLEL:

# *.bin variants here to let them survive a 'make clean'
all: hets.bin hets_server.bin

# Documentation (no haddock stuff, i.e. "docs/index.html", since developer can
# generate it on demand by themselves and other users dont't need it). Other
# papers (doc/*.pdf) are already pre-generated.
docs: doc/UserGuide.pdf

# Upgrade haskell-stack
stack_upgrade:
	$(STACK) $(STACK_OPTS) upgrade
	$(STACK_EXEC) -- ghc-pkg recache
# Create the build environment
stack: $(STACK_UPGRADE_TARGET)
	$(STACK) $(STACK_OPTS) build --install-ghc --only-dependencies $(STACK_DEPENDENCIES_FLAGS)
	touch stack
restack:
	rm -f stack
	$(STACK) $(STACK_OPTS) build --install-ghc --only-dependencies $(STACK_DEPENDENCIES_FLAGS)
	touch stack

SED := $(shell [ "$(OSNAME)" = 'SunOS' ] && printf 'gsed' || printf 'sed')
TAR := $(shell [ "$(OSNAME)" = 'SunOS' ] && printf 'gtar' || printf 'tar')
INSTALL := $(shell [ "$(OSNAME)" = 'SunOS' ] && printf 'ginstall' || printf 'install')
HETS_VERSION ?= $(shell ${SED} -n \
	-e '/^hetsVersionNumeric =/ { s/.*"\([^"]*\)".*/\1/; p; q; }' \
	Driver/Version.hs )

define EOL


endef

# indicate, whether working on an exported repo
EXPORTED := $(shell [ -d .git ] || printf 1)

# the 'replacing spaces' example was taken from the (GNU) Make info manual
empty =
space = $(empty) $(empty)


DRIFT_deps = utils/DrIFT-src/*hs
GENERATERULES_deps = utils/GenerateRules/*hs $(DRIFT_deps)
GENITCORRECTIONS_deps = utils/itcor/GenItCorrections.hs

PERL = perl
GENRULES = utils/genRules
GENRULECALL = $(GENRULES) -r ShATermConvertible \
    -i ATerm.Lib

GENRULECALL2 = $(GENRULES) -r ShATermLG \
    -i ATerm.Lib -i ATC.Grothendieck
DRIFT = utils/DrIFT
HADDOCK = haddock

DTD2HS = utils/DtdToHaskell
ifneq ($(strip $(HAXML_PACKAGE_COMPAT)),)
DTD2HS_src = utils/DtdToHaskell-src/pre-1.22/
else
DTD2HS_src = utils/DtdToHaskell-src/current/
endif

ifneq ($(strip $(HAXML_PACKAGE)),)
derived_sources += Isabelle/IsaExport.hs
endif

DTD2HS_deps = $(DTD2HS_src)*.hs

# list glade files
GTK_GLADE_FILES = $(wildcard GUI/Glade/*.glade)
GTK_GLADE_HSFILES = $(subst .glade,.hs,$(GTK_GLADE_FILES))

derived_sources += $(GTK_GLADE_HSFILES)

# the list of logics that need ShATermConvertible instances
logics = CASL HasCASL Isabelle Modal Hybrid TopHybrid Temporal \
    CoCASL COL CspCASL CASL_DL \
    SoftFOL ConstraintCASL Propositional RelationalScheme VSE OMDoc DFOL \
    LF Framework Maude ExtModal CommonLogic CSL QBF Adl HolLight Fpl THF \
    FreeCAD OWL2 RDF CSMOF QVTR TPTP

TESTTARGETFILES += Scratch.hs CASL/fromKif.hs CASL/capa.hs HasCASL/hacapa.hs \
    Haskell/wrap.hs Isabelle/isa.hs Syntax/hetpa.hs \
    ATC/ATCTest.hs ATC/ATCTest2.hs Common/ATerm/ATermLibTest.hs \
    Common/ATerm/ATermDiffMain.hs Common/annos.hs \
    SoftFOL/tests/PrintTPTPTests.hs Comorphisms/test/showKP.hs \
    Comorphisms/test/sublogicGraph.hs PGIP/ParseProofScript.hs \
    Common/testxupdate.hs Common/testxpath.hs \
    SoftFOL/dfg.hs Adl/adl.hs GUI/displayDependencyGraph.hs

### list of directories to run checks in
TESTDIRS += Common CASL Fpl/test HasCASL test ExtModal/Tries \
    CommonLogic/TestData

hs_clean_files = Haskell/TiATC.hs Haskell/TiDecorateATC.hs \
    Haskell/TiPropATC.hs Haskell/ATC_Haskell.der.hs


ifneq ($(PFE_FLAGS),)
PFE_TOOLDIR := $(wildcard $(dir $(PFE_SETUP)))
PFE_DIRS := base/AST base/TI base/parse2 base/parse2/Lexer base/parse2/Parser \
    base/parse2/LexerGen base/parse2/LexerSpec base/tests/HbcLibraries \
    base/pretty base/syntax base/lib base/lib/Monads base/Modules base/defs \
    base/transforms base/transforms/Deriving property \
    property/syntax property/AST property/transforms \
    property/TI property/defs property/parse2 property/parse2/Parser

PFE_PATHS := $(addprefix $(PFE_TOOLDIR)/, $(PFE_DIRS))
DRIFT_ENV := DERIVEPATH=$(subst $(space),:,$(PFE_PATHS))

logics += Haskell
derived_sources += Haskell/PreludeString.hs

APPENDPRELUDESTRING = utils/appendHaskellPreludeString \
    Haskell/ProgramaticaPrelude.hs

## rule for appendHaskellPreludeString
Haskell/PreludeString.hs: Haskell/PreludeString.append.hs \
    $(APPENDPRELUDESTRING)
	$(APPENDPRELUDESTRING) < $< > $@

Ast_Haskell_files = HsDeclStruct HsExpStruct HsFieldsStruct \
    HsGuardsStruct HsKindStruct HsPatStruct HsTypeStruct HsAssocStruct \
    HsModule HsName HsLiteral HsIdent

#files in base/TI/
#Ti_Haskell_files = TiTypes TiKinds TiDecorate TiInstanceDB

#Ti_Prop_files = property/TI/TiPropDecorate property/syntax/PropSyntaxRec

Other_PFE_files := property/AST/HsPropStruct base/defs/PNT \
    base/defs/UniqueNames base/Modules/TypedIds base/Modules/Ents \
    base/parse2/SourceNames base/syntax/SyntaxRec \
    property/syntax/PropSyntaxStruct

Haskell_files := $(addsuffix .hs, \
    $(addprefix $(PFE_TOOLDIR)/base/AST/, $(Ast_Haskell_files)) \
    $(addprefix $(PFE_TOOLDIR)/, $(Other_PFE_files)))

## rule for ATC generation
Haskell/ATC_Haskell.der.hs: $(Haskell_files) $(GENRULES)
	$(GENRULECALL) -r Typeable -i Data.Typeable -i Haskell.BaseATC \
		-o $@ $(Haskell_files)

hs_der_files += $(hs_clean_files)

TESTDIRS += ToHaskell
TESTTARGETFILES += Haskell/hana.hs Haskell/h2h.hs Haskell/h2hf.hs
else
DRIFT_ENV := DERIVEPATH=
endif
# end of programatica stuff (PFE_FLAGS)

TESTTARGETS := $(subst .hs,,$(TESTTARGETFILES))



# files generated by DriFT
drifted_files = Common/AS_Annotation.hs \
    CASL/AS_Basic_CASL.hs Modal/AS_Modal.hs Hybrid/AS_Hybrid.hs TopHybrid/AS_TopHybrid.hs  \
    Syntax/AS_Structured.hs Syntax/AS_Architecture.hs Syntax/AS_Library.hs \
    Propositional/AS_BASIC_Propositional.hs \
    CoCASL/AS_CoCASL.hs COL/AS_COL.hs \
    CASL_DL/AS_CASL_DL.hs THF/As.hs \
    CspCASL/AS_CspCASL_Process.hs CspCASL/AS_CspCASL.hs \
    RelationalScheme/AS.hs ATC/Grothendieck.hs \
    ExtModal/AS_ExtModal.hs QBF/AS_BASIC_QBF.hs \
    CommonLogic/AS_CommonLogic.hs Fpl/As.hs \
	TPTP/AS.hs \
    $(gendrifted_files)

# files to extract data types from to generate ShATermConvertible instances
atc_files = Common/AS_Annotation.der.hs Common/DefaultMorphism.hs \
    Syntax/AS_Structured.der.hs Syntax/AS_Architecture.der.hs \
    Common/GlobalAnnotations.hs Syntax/AS_Library.der.hs \
    Logic/Prover.hs Common/LibName.hs Common/ExtSign.hs \
    Common/Consistency.hs Common/ProofTree.hs \
    Static/DgUtils.hs Static/XGraph.hs Static/DevGraph.hs \
    Common/Id.hs Common/Result.hs Common/OrderedMap.hs \
    Common/Lib/Graph.hs Common/IRI.hs

# files generated by genRules as input for DriFT
atc_der_files = $(foreach file, $(atc_files), \
    ATC/$(basename $(basename $(notdir $(file)))).der.hs)

# the rules to create ATC .der.hs file for DriFT
ATC/Id.der.hs: Common/Id.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/IRI.der.hs: Common/IRI.hs $(GENRULES)
	$(GENRULECALL) -i ATC.Id -o $@ $<

ATC/Result.der.hs: Common/Result.hs $(GENRULES)
	$(GENRULECALL) -i ATC.Id -o $@ $<

ATC/OrderedMap.der.hs: Common/OrderedMap.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/Graph.der.hs: Common/Lib/Graph.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/ProofTree.der.hs: Common/ProofTree.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/AS_Annotation.der.hs: Common/AS_Annotation.der.hs $(GENRULES)
	$(GENRULECALL) -i ATC.IRI -i Common.ATerm.ConvInstances -o $@ $<

ATC/Consistency.der.hs: Common/Consistency.hs $(GENRULES)
	$(GENRULECALL) -x Common.Consistency.ConservativityChecker -o $@ $<

ATC/LibName.der.hs: Common/LibName.hs $(GENRULES)
	$(GENRULECALL) -i ATC.IRI -i Common.ATerm.ConvInstances -o $@ $<

ATC/ExtSign.der.hs: Common/ExtSign.hs $(GENRULES)
	$(GENRULECALL) -i Common.ATerm.ConvInstances -o $@ $<

ATC/DefaultMorphism.der.hs: Common/DefaultMorphism.hs $(GENRULES)
	$(GENRULECALL) -o $@ $<

ATC/AS_Structured.der.hs: Syntax/AS_Structured.der.hs $(GENRULES)
	$(GENRULECALL2) -o $@ $<

ATC/AS_Architecture.der.hs: Syntax/AS_Architecture.der.hs $(GENRULES)
	$(GENRULECALL2) -i ATC.AS_Structured -o $@ $<

ATC/AS_Library.der.hs: Syntax/AS_Library.der.hs $(GENRULES)
	$(GENRULECALL2) -i ATC.AS_Architecture -i ATC.LibName -o $@ $<

ATC/GlobalAnnotations.der.hs: Common/GlobalAnnotations.hs $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -i ATC.Result -o $@ $<

ATC/Prover.der.hs: Logic/Prover.hs $(GENRULES)
	$(GENRULECALL) -x Logic.Prover.ProverTemplate \
            -x Logic.Prover.ConsChecker \
            -i ATC.AS_Annotation -i ATC.OrderedMap -o $@ $<

ATC/DgUtils.der.hs: Static/DgUtils.hs $(GENRULES)
	$(GENRULECALL2) -i ATC.LibName -i ATC.Consistency -o $@ $<

ATC/XGraph.der.hs: Static/XGraph.hs $(GENRULES)
	$(GENRULECALL2) -i ATC.DgUtils -o $@ $<

ATC/DevGraph.der.hs: Static/DevGraph.hs $(GENRULES)
	$(GENRULECALL2) -i ATC.XGraph -i ATC.AS_Library -o $@ $<

# ATC files for every logic
CASL_files = CASL/Sublogic.hs CASL/Morphism.hs CASL/Sign.hs \
    CASL/AS_Basic_CASL.der.hs

HasCASL_files = Common/Prec.hs HasCASL/As.hs HasCASL/Le.hs HasCASL/Sublogic.hs
Isabelle_files = Isabelle/IsaSign.hs

Propositional_files = Propositional/Sign.hs Propositional/Morphism.hs \
    Propositional/AS_BASIC_Propositional.hs Propositional/Symbol.hs \
    Propositional/Sublogic.hs

HolLight_files = HolLight/Sentence.hs HolLight/Sign.hs \
                 HolLight/Sublogic.hs HolLight/Term.hs

QBF_files = Propositional/Sign.hs QBF/Morphism.hs \
    QBF/AS_BASIC_QBF.hs QBF/Symbol.hs \
    QBF/Sublogic.hs

RS_files = RelationalScheme/AS.hs RelationalScheme/Sign.hs

Modal_files = Modal/AS_Modal.hs Modal/ModalSign.hs
Hybrid_files = Hybrid/AS_Hybrid.hs Hybrid/HybridSign.hs
TopHybrid_files = TopHybrid/AS_TopHybrid.hs TopHybrid/TopHybridSign.hs

Temporal_files = Temporal/AS_BASIC_Temporal.hs Temporal/Sign.hs \
    Temporal/Symbol.hs Temporal/Morphism.hs

ConstraintCASL_files = ConstraintCASL/AS_ConstraintCASL.hs
CoCASL_files = CoCASL/AS_CoCASL.hs CoCASL/CoCASLSign.hs
COL_files = COL/AS_COL.hs COL/COLSign.hs

CspCASL_files = CspCASL/AS_CspCASL.hs CspCASL/AS_CspCASL_Process.hs \
    CspCASL/SignCSP.hs CspCASL/SymbItems.hs CspCASL/Symbol.hs \
    CspCASL/Morphism.hs

CASL_DL_files = CASL_DL/AS_CASL_DL.hs CASL_DL/Sign.hs CASL_DL/Sublogics.hs
SoftFOL_files = SoftFOL/Sign.hs
VSE_files = VSE/As.hs
OMDoc_files = OMDoc/OMDocInterface.hs
DFOL_files = DFOL/AS_DFOL.hs DFOL/Sign.hs DFOL/Morphism.hs DFOL/Symbol.hs
LF_files = LF/Sign.hs LF/Morphism.hs LF/AS.hs
Framework_files = Framework/AS.hs

Maude_files = Maude/Sign.hs Maude/Morphism.hs Maude/Sentence.hs \
    Maude/Symbol.hs Maude/AS_Maude.hs

ExtModal_files = ExtModal/AS_ExtModal.hs ExtModal/ExtModalSign.hs \
    ExtModal/MorphismExtension.hs ExtModal/Sublogic.hs

CSL_files = CSL/Sign.hs CSL/Morphism.hs CSL/AS_BASIC_CSL.hs CSL/Symbol.hs \
    CSL/TreePO.hs

CommonLogic_files = CommonLogic/AS_CommonLogic.hs CommonLogic/Sign.hs \
  CommonLogic/Symbol.hs CommonLogic/Morphism.hs CommonLogic/Sublogic.hs

Adl_files = Adl/As.hs Adl/Sign.hs

Fpl_files = Fpl/As.hs Fpl/Sign.hs

THF_files = THF/As.hs THF/Cons.hs THF/Sign.hs THF/Sublogic.hs

FreeCAD_files = FreeCAD/As.hs

OWL2_files = OWL2/AS.hs OWL2/Symbols.hs OWL2/Sign.hs OWL2/MS.hs \
  OWL2/Morphism.hs OWL2/ProfilesAndSublogics.hs OWL2/Sublogic.hs \
  OWL2/Profiles.hs Common/IRI.hs

RDF_files = RDF/AS.hs OWL2/AS.hs RDF/Symbols.hs RDF/Sign.hs RDF/Morphism.hs \
  RDF/Sublogic.hs Common/IRI.hs

CSMOF_files = CSMOF/As.hs CSMOF/Sign.hs

QVTR_files = QVTR/As.hs QVTR/Sign.hs

TPTP_files = TPTP/AS.hs TPTP/Sign.hs TPTP/Sublogic.hs

# ATC DrIFT-rule generation for logics
CASL/ATC_CASL.der.hs: $(CASL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ $(CASL_files)

RelationalScheme/ATC_RelationalScheme.der.hs: $(RS_files) $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ $(RS_files)

Propositional/ATC_Propositional.der.hs: $(Propositional_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(Propositional_files)

QBF/ATC_QBF.der.hs: $(QBF_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(QBF_files)


HolLight/ATC_HolLight.der.hs: $(HolLight_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(HolLight_files)

HasCASL/ATC_HasCASL.der.hs: $(HasCASL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ $(HasCASL_files)

Isabelle/ATC_Isabelle.der.hs: $(Isabelle_files) $(GENRULES)
	$(GENRULECALL) -o $@ $(Isabelle_files)

Modal/ATC_Modal.der.hs: $(Modal_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(Modal_files)

Hybrid/ATC_Hybrid.der.hs: $(Hybrid_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(Hybrid_files)

TopHybrid/ATC_TopHybrid.der.hs: $(TopHybrid_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(TopHybrid_files)

Temporal/ATC_Temporal.der.hs: $(Temporal_files) $(GENRULES)
	$(GENRULECALL) -i CASL.ATC_CASL -o $@ $(Temporal_files)

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

VSE/ATC_VSE.der.hs: $(VSE_files) $(GENRULES)
	$(GENRULECALL) -x VSE.As.FoldRec -i CASL.ATC_CASL -o $@ $(VSE_files)

OMDoc/ATC_OMDoc.der.hs: $(OMDoc_files) $(GENRULES)
	$(GENRULECALL) -i ATC.IRI -o $@ $(OMDoc_files)

DFOL/ATC_DFOL.der.hs: $(DFOL_files) $(GENRULES)
	$(GENRULECALL)  -i ATC.AS_Annotation -o $@ $(DFOL_files)

LF/ATC_LF.der.hs: $(LF_files) $(GENRULES)
	$(GENRULECALL)	-i ATC.AS_Annotation -o $@ $(LF_files)

Framework/ATC_Framework.der.hs: $(Framework_files) $(GENRULES)
	$(GENRULECALL)	-i ATC.AS_Annotation -o $@ $(Framework_files)

Maude/ATC_Maude.der.hs: $(Maude_files) $(GENRULES)
	$(GENRULECALL)  -i ATC.AS_Annotation -o $@ $(Maude_files)

ExtModal/ATC_ExtModal.der.hs: $(ExtModal_files) $(GENRULES)
	$(GENRULECALL)  -i CASL.ATC_CASL -o $@ $(ExtModal_files)

CSL/ATC_CSL.der.hs: $(CSL_files) $(GENRULES)
	$(GENRULECALL) -i ATC.AS_Annotation -o $@ $(CSL_files)

CommonLogic/ATC_CommonLogic.der.hs: $(CommonLogic_files) $(GENRULES)
	$(GENRULECALL)  -i ATC.AS_Annotation -o $@ $(CommonLogic_files)

Adl/ATC_Adl.der.hs: $(Adl_files) $(GENRULES)
	$(GENRULECALL)  -i ATC.AS_Annotation -o $@ $(Adl_files)

Fpl/ATC_Fpl.der.hs: $(Fpl_files) $(GENRULES)
	$(GENRULECALL)  -i CASL.ATC_CASL -o $@ $(Fpl_files)

THF/ATC_THF.der.hs: $(THF_files) $(GENRULES)
	$(GENRULECALL) -i ATC.Id -i ATC.GlobalAnnotations -o $@ $(THF_files)

FreeCAD/ATC_FreeCAD.der.hs: $(FreeCAD_files) $(GENRULES)
	$(GENRULECALL) -i Common.ATerm.ConvInstances -o $@ $(FreeCAD_files)

OWL2/ATC_OWL2.der.hs: $(OWL2_files) $(GENRULES)
	$(GENRULECALL) -i ATC.Result -o $@ $(OWL2_files)

RDF/ATC_RDF.der.hs: $(RDF_files) $(GENRULES)
	$(GENRULECALL) -i ATC.Result -o $@ $(RDF_files)

CSMOF/ATC_CSMOF.der.hs: $(CSMOF_files) $(GENRULES)
	$(GENRULECALL) -i Common.ATerm.ConvInstances -o $@ $(CSMOF_files)

QVTR/ATC_QVTR.der.hs: $(QVTR_files) CSMOF/ATC_CSMOF.hs $(GENRULES)
	$(GENRULECALL) -i CSMOF.ATC_CSMOF -i Common.ATerm.ConvInstances \
 -o $@ $(QVTR_files)

TPTP/ATC_TPTP.der.hs: $(TPTP_files) $(GENRULES)
	$(GENRULECALL)  -i ATC.AS_Annotation -o $@ $(TPTP_files)

# all ATC .der.hs files for all logics
atc_logic_files = $(foreach logic, $(logics), $(logic)/ATC_$(logic).der.hs)

generated_rule_files = $(atc_der_files) $(atc_logic_files)

# a rule to create all .der.hs files
genRules: $(generated_rule_files)

# the final ATC target files created by DriFT
gendrifted_files = $(patsubst %.der.hs, %.hs, $(generated_rule_files))

# all sources that need to be created before ghc can be called
derived_sources += $(drifted_files) $(hs_der_files)


####################################################################
# BUILD related targets
####################################################################
.PHONY: all hets-opt hets-optimized hets_server-opt docs jars \
	clean o_clean clean_pretty bin_clean java_clean realclean distclean \
	annos check test capa hacapa h2h h2hf showKP clean_genRules genRules \
    count fromKif release cgi ghci build-hets callghc \
	get-programatica check_desktop check_server check_cgi \
	install install-common install-owl-tools archive \
	build-indep build-arch build binary-indep binary-arch binary

.SECONDARY: $(generated_rule_files)

.PRECIOUS: %.bin

# dummy target to force ghc invocation
callghc:

# some trickery to trigger a full clean if the main target (hets, hets_server)
# changed since last call
check_desktop:
	-@[ -e .hets_server -o -e .hets_cgi -o -e .hets_oow ] && $(MAKE) clean

check_server:
	-@[ -e .hets_desktop -o -e .hets_cgi -o -e .hets_oow ] && $(MAKE) clean

check_cgi:
	-@[ -e .hets_desktop -o -e .hets_server -o -e .hets_oow ] && $(MAKE) clean

%-opt: HC_OPTS += -O

# the variant without GUI
hets_server hets_server-opt: HASKELINE_PACKAGE :=
hets_server hets_server-opt: GLADE_PACKAGE :=
hets_server hets_server-opt: UNI_PACKAGE :=
hets_server hets_server-opt: check_server $(derived_sources)
	@touch .hets_server
	$(HC) --make $(HC_OPTS) -o hets_server hets.hs
	@ln -f hets_server hets_server.bin

hets-opt: check_desktop $(derived_sources)
	@touch .hets_desktop
	$(HC) --make $(HC_OPTS) -o hets hets.hs
	@ln -f hets hets.bin

# deprecated target name
hets-optimized: hets-opt

hets_cgi hets_cgi-opt: check_cgi GUI/hets_cgi.hs $(derived_sources)
	@touch .hets_cgi
	$(HC) --make $(HC_OPTS) -o hets.cgi GUI/hets_cgi.hs
	@ln -f hets.cgi hets_cgi.bin

derivedSources: $(derived_sources)

TEX_FILES := $(wildcard doc/*.tex doc/*.png doc/*.dot doc/*.sty doc/*.eps)
doc/UserGuide.pdf: $(TEX_FILES)
	@X=`which latexmk 2>/dev/null` ; \
	if [ -n "$$X" ]; then \
		cd doc ; latexmk -silent -pdf -use-make \
			-pdflatex="pdflatex -interaction=nonstopmode" UserGuide.tex ; \
	else \
		printf '\nMissing "latexmk" - unable to create doc/UserGuide.pdf!\n\n';\
	fi

# 	replace '$Header$' in all *.hs with the filename of the containing file
#	call it from time to time
updateHeaders: $(derived_sources)
	@find . -name '*.hs' -exec fgrep -l '$$Header$$' {} + | xargs -I@ \
		${SED} -i -e 's|\$$Header\$$|@|g' @

GHC_LIBDIR := $(shell $(STACK_EXEC) ghc --print-libdir)
GHC_BASEDIR := $(shell cd $(GHC_LIBDIR)/../.. && printf "$${PWD}")

# scanning the "whole" NFS server isn't so smart, so restrict to wellknown dirs
HADDOCK_INTERFACES = $(shell find $(GHC_BASEDIR)/share/doc/ghc \
	$(GHC_BASEDIR)/lib/ghc-doc/haddock -name '*.haddock' 2>/dev/null)

HAD_INTS = $(foreach file, $(HADDOCK_INTERFACES),\
 -i http://hackage.haskell.org/packages/archive/$(basename $(notdir $(file)))/latest/doc/html,$(file))

HADDOCK_OPTS := $(addprefix --optghc=, $(HC_OPTS))
docs/index.html: $(derived_sources)
	@$(RM) -r docs && mkdir docs && \
		printf '\nCheck log.haddock for results ...\n'
	$(HADDOCK) -o docs -h -s ../%F $(HAD_INTS) \
            -t 'Hets - the Heterogeneous Tool Set' \
            -p Hets-Haddock-Prologue.txt $(HADDOCK_OPTS) \
             $(filter-out Scratch.hs, $(wildcard *.hs)) \
		>log.haddock 2>&1


$(DRIFT): $(DRIFT_deps)
	cd utils/DrIFT-src; $(HC) --make -o ../DrIFT DrIFT.hs

$(DTD2HS): $(DTD2HS_deps) utils/DtdToHaskell-src/DtdToHaskell.hs
	@mkdir -p utils/DtdToHaskell-src/DtdToHaskell
	@cp -f $(DTD2HS_deps) utils/DtdToHaskell-src/DtdToHaskell
	$(HC) --make $(HC_OPTS) -iutils/DtdToHaskell-src -o $@ \
            utils/DtdToHaskell-src/DtdToHaskell.hs

Isabelle/IsaExport.hs: $(DTD2HS) Isabelle/IsaExport.dtd
	$(DTD2HS) Isabelle/IsaExport.dtd Isabelle/IsaExport.hs Isabelle.

$(GENRULES): $(DRIFT) $(GENERATERULES_deps)
	@cd utils/GenerateRules; \
	$(HC) --make -i../DrIFT-src -i../.. $(HC_WARN) \
		-o ../genRules GenerateRules.hs

utils/appendHaskellPreludeString: utils/appendHaskellPreludeString.hs
	$(HC) --make -o $@ $<

# Common/LaTeX_maps.hs generation
utils/genItCorrections: $(GENITCORRECTIONS_deps)
	$(HC) --make -o $@ $<

pretty/LaTeX_maps.hs: utils/words.pl utils/genItCorrections \
    pretty/words.input pretty/fonts.input pretty/width-table.tex.templ
	$(info $(EOL)Generating pretty/LaTeX_maps.hs ...$(EOL))
	@cd pretty >/dev/null; \
	$(PERL) ../utils/words.pl > words.pl.log ; \
	../utils/genItCorrections gen_it_characters gen_it_words >> LaTeX_maps.hs
	$(info $(EOL)Done.$(EOL)Please copy the file manually to Common$(EOL))

### clean up
clean_stack:
	@$(RM) -rf .stack-work stack

clean_genRules:
	@$(RM) $(generated_rule_files) $(gendrifted_files) $(hs_clean_files)

### removes all *.o, *.hi and *.p_o files in all subdirectories except for
### .stack-work, where the compiled dependencies reside
o_clean:
	@find . -path ./.stack-work -prune -type f \
	    -o \( -name '*.o' -o -name '*.hi' -o -name '*.p_o' \
        -o -name '*.dyn_hi' -o -name '*.dyn_o' \) -exec rm -f {} +
	@$(RM) -f .hets*

### remove binaries
bin_clean:
	@$(RM) hets hets.cgi hets_server \
		$(TESTTARGETS)

# do not delete on exported archive, because latexmk might not be available
USER_GUIDE := $(shell [ -n "$(EXPORTED)" ] || printf 'doc/UserGuide.pdf')

# Ubuntu/Debian dash crap really hurts
clean_pretty:
	@ksh -c "rm -rf pretty/*.c.* pretty/*.h.* pretty/gen_it_* \
			pretty/generated_words.tex \
		test/*/*.{thy,pp.dol,pp.tex,th,dfg.c,xml,log,dvi,aux,sty} \
			test/*/log */test/temp* ToHaskell/test/*.{out,output} \
			ExtModal/Tries/*.{pp.dol,th} Fpl/test/*.{pp.dol,th} \
			CommonLogic/TestData/*.{pp.dol,th} Common/testxmldiff \
		doc/UserGuide.{log,aux,bbl,blg,out,fdb_latexmk,fls} doc/hs2isa.ps \
			$(USER_GUIDE) log.haddock \
		debian/{root,files,hets-*,tmp} \
	"

java_clean:
	@$(RM) -rf OWL2/*.jar OWL2/java/build OWL2/java/tmp OWL2/lib

clean: bin_clean o_clean clean_pretty

realclean: clean java_clean
	@$(RM) -f *.bin debian/changelog*

### additionally removes generated files not in the repository tree
distclean: clean_stack realclean clean_genRules
	@$(RM) -rf $(derived_sources) \
		utils/appendHaskellPreludeString \
		utils/DrIFT utils/genRules \
		$(DTD2HS) \
		utils/DtdToHaskell-src/DtdToHaskell \
		utils/genItCorrections pretty/LaTeX_maps.hs pretty/words.pl.log \
		docs

### interactive
ghci: $(derived_sources)
	$(STACK_EXEC) ghci $(HC_OPTS)

### build only, don't link. Target was formerly known as 'build'.
build-hets: hets.hs
	@touch .hets-oow
	$(HC) --make $(HC_OPTS) -c $<

### Kif parser
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
	$(HC) -O --make $(HC_OPTS) -o $@ $<

### HasCASL to Haskell translation
h2h: Haskell/h2h

### test program to check the known provers
showKP: Comorphisms/test/showKP

### run tests in other directories
check: $(TESTTARGETS)
	for i in $(TESTDIRS); do $(MAKE) -C $$i check; done

test:
	yes X | $(MAKE) check

ATC/DevGraph.hs: Static/DevGraph.hs

## two dependencies to avoid circular prerequisites
CASL_DEPENDENT_BINARIES = hets CASL/capa CASL/fromKif \
   Common/annos Common/test_parser Comorphisms/test/showKP \
   CspCASL/print_csp HasCASL/hacapa Haskell/h2h Haskell/h2hf \
   Haskell/hana Haskell/wrap Isabelle/isa Syntax/hetpa

$(CASL_DEPENDENT_BINARIES): $(derived_sources)

## suffix rules
.SUFFIXES:

## rule for GHC
%: %.hs $(STACK_TARGET) callghc
	@touch .hets-oow
	$(HC) --make $(HC_OPTS) -o $@ $<

## rule for DrIFT
%.hs: %.der.hs $(DRIFT)
	$(DRIFT_ENV); export DERIVEPATH; $(DRIFT) $< > $@

## compiling rules for object and interface files
%.o %.hi: %.hs
	$(HC) $(HC_OPTS) -c $<

%.o %.hi: %.lhs
	$(HC) $(HC_OPTS) -c $<

## compiling rules for dependencies
%.d : %.hs
	$(HC) -M $(HC_OPTS) -optdep-f -optdep$@ $<

%.d : %.lhs
	$(HC) -M $(HC_OPTS) -optdep-f -optdep$@ $<

## Rule to generate hs files from glade files. Needed for GTK
%.hs: %.glade utils/appendHaskellPreludeString \
  GUI/Glade/Template.append.hs
	b=`basename $< .glade`; \
    cat GUI/Glade/Template.append.hs | sed "s/\%s/$$b/" | \
    utils/appendHaskellPreludeString $< > $@


# just build all required jar files
jars:
	@cd OWL2/java ; ant -S



PFE_BASE := $(dir $(PFE_SETUP_FILE))
get-programatica:
	@if [ -z $(PROGRAMATICA_SRC_FILE) -o ! -e $(PROGRAMATICA_SRC_FILE) ] && \
		[ -z "$(PROGRAMATICA_SRC_URL)" ]; then \
		printf 'Unable to get programatica (%s %s)\n' \
			'neither PROGRAMATICA_SRC_FILE nor PROGRAMATICA_SRC_FILE' \
			'environment variable is set/exist.' ; \
		exit 1 ; \
	fi
	@if [ -e $(PFE_BASE) ]; then \
		printf '%s already exists.\n' $(PFE_BASE) ; \
		exit 2 ; \
	fi
	-@HWD=$${PWD} ; X=`echo $(PFE_BASE)| cut -f1 -d/`; \
	rm -f $$X 2>/dev/null || rm -rf $(PFE_BASE) ; \
	mkdir -p $(PFE_BASE); \
	cd $(PFE_BASE) || exit 3 ; \
	PFEDIR=$${PWD} ; cd .. ; \
	if [ -n $(PROGRAMATICA_SRC_FILE) -a -e $(PROGRAMATICA_SRC_FILE) ]; then \
		printf 'Extracting $(PROGRAMATICA_SRC_FILE) ...\n' ; \
		if $(TAR) xzf "$(PROGRAMATICA_SRC_FILE)" ; then \
			mv programatica-*/* $${PFEDIR}/ && rmdir programatica-* ; \
		fi ; \
	fi ; \
	if [ -n "$(PROGRAMATICA_SRC_URL)" -a ! -e $${HWD}/$(PFE_SETUP_FILE) ]; then\
		printf 'Fetching $(PROGRAMATICA_SRC_URL) ...\n' ; \
		if wget --no-verbose -O x.tgz "$(PROGRAMATICA_SRC_URL)" ; then \
			if $(TAR) xzf x.tgz ; then \
				mv programatica-*/* $${PFEDIR}/ && rmdir programatica-* ; \
				rm -f x.tgz ; \
			fi ; \
		fi ; \
	fi
	@if [ -e $(PFE_SETUP_FILE) ]; then \
		printf 'Programatica support available.\nYou probably need to %s\n\n' \
			'"make distclean" and make the desired target again.' ; \
	else \
		rm -rf $(PFE_BASE) ; \
		printf 'Failed! No programatica support available!\n' ; exit 4 ; \
	fi

ARC_NAME ?= /tmp/hets-$(HETS_VERSION)-src.tar.xz

# remove trailing .txz or .tar.xz
archive: ARC_BNAME = \
	$(patsubst %.txz,%, $(patsubst %.tar.xz,%,$(notdir $(ARC_NAME))))

archive: $(USER_GUIDE)
	@[ -n "$(EXPORTED)" ] && \
		printf '\nThis source tree is already exported.\n' && exit 1 ; \
	FNAME=$(dir $(ARC_NAME))/$(ARC_BNAME).tar.xz ; \
	printf "Exporting source to $${FNAME} ...\n" ; \
	rm -rf tmp ; mkdir tmp || exit 3 ; \
	git archive --format=tar --prefix=$(ARC_BNAME)/ HEAD | \
		( cd tmp ; $(TAR) xf - ) ; \
	if [ -e $(USER_GUIDE) ]; then \
		cp $(USER_GUIDE) tmp/$(ARC_BNAME)/$(USER_GUIDE) ; \
	else \
		printf '\nWARNING: No $(USER_GUIDE) is unavailable\n!' ; \
	fi ; \
	cd tmp/$(ARC_BNAME) ; $(MAKE) distclean ; \
	printf 'Removing unused/non-distributed files ...\n' ; \
	rm -rf HolLight/OcamlTools/*/*dmtcp OWL2/java/lib/native \
		MMT/hets-mmt-standalone.jar ; \
	rm -rf GMP mini .gitignore utils/{nightly,debian,macports,ubuntu} ; \
	zip -d OWL2/java/lib/owlapi-osgidistribution-3.5.2.jar \
		lib/guava-18.0.jar lib/trove4j-3.0.3.jar ; \
	printf 'Done.\n' ; \
	cd .. ; $(TAR) cJf $(ARC_BNAME).tar.xz $(ARC_BNAME) || exit 4 ; \
	cd .. ; \
	ln $${PWD}/tmp/$(ARC_BNAME).tar.xz $${FNAME} 2>/dev/null || \
		mv -f $${PWD}/tmp/$(ARC_BNAME).tar.xz $${FNAME} ; \
	ls -l $${FNAME}
	$(info $(EOL)The next "make clean" will remove the tmp/ directory used.$(EOL))

#############################################################################
# INSTALL targets
#############################################################################
# We use $DEB_BUILD_ARCH to detect, whether this make got triggered via
# dpkg-buildpackage
DEFAULT_DESTDIR := \
	$(shell [ -n "$$DEB_BUILD_ARCH" ] && printf "$$PWD/debian/root")
SUBDIR_common := \
	$(shell [ -n "$$DEB_BUILD_ARCH" ] && printf '/common')
SUBDIR_hets := \
	$(shell [ -n "$$DEB_BUILD_ARCH" ] && printf '/desktop')
SUBDIR_hets_server := \
	$(shell [ -n "$$DEB_BUILD_ARCH" ] && printf '/server')
DEFAULT_DIST_TEX_LATEX := \
	$(shell [ "$(OSNAME)" = 'SunOS' ] && printf 'share/texmf/dist/tex/latex' ||\
		printf 'share/texlive/texmf-dist/tex/latex')

DESTDIR ?= $(DEFAULT_DESTDIR)
PREFIX ?= /usr

# all _relative_ wrt. $(PREFIX) and w/o trailing slashes
HETS_DIR := lib/hets
DOC_DIR ?= share/doc/hets
MAN_DIR ?= share/man/man1
DIST_LATEX ?= $(DEFAULT_DIST_TEX_LATEX)

# see OWL2/ProveFact.hs - it doesn't use OSGi so we need to extract JNI libs
install-owl-tools: \
	BASEDIR = $(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)/hets-owl-tools
install-owl-tools: jars
	$(INSTALL) -m 0755 -d \
		$(BASEDIR)/lib/native/i686 \
		$(BASEDIR)/lib/native/x86_64 \
		$(BASEDIR)/tests
	$(INSTALL) -m 0644 OWL2/tests/wine.rdf $(BASEDIR)/tests/
	$(INSTALL) -m 0644 OWL2/*.jar $(BASEDIR)/
	ln -sf ../CASL/Termination/AProVE.jar $(BASEDIR)/AProVE.jar
	ln -sf ../DMU/OntoDMU.jar $(BASEDIR)/OntoDMU.jar
	$(INSTALL) -m 0644 OWL2/java/lib/*.jar $(BASEDIR)/lib/
	$(info Extracting/removing JNI libs from factplusplus*.jar ...$(EOL))
	rm -rf OWL2/java/tmp ; mkdir -p OWL2/java/tmp; cd OWL2/java/tmp ; \
	X=`ls ../lib/uk.ac.manchester.cs.owl.factplusplus*.jar` ; \
	jar xf $$X ; \
	$(INSTALL) -m 0755 lib/native/32bit/libFaCTPlusPlusJNI.* \
		$(BASEDIR)/lib/native/i686/ ; \
	$(INSTALL) -m 0755 lib/native/64bit/libFaCTPlusPlusJNI.* \
		$(BASEDIR)/lib/native/x86_64/; \
	rm -rf $(BASEDIR)/lib/native/*/*.dll lib \
		$(BASEDIR)/lib/`basename $$X` ; \
	jar cMf $(BASEDIR)/lib/`basename $$X` *
	-zip -d $(BASEDIR)/lib/owlapi-osgidistribution-3.5.2.jar \
		lib/guava-18.0.jar lib/trove4j-3.0.3.jar
	@printf 'Sources:\n\t%s\n\t%s\n\t%s\n' \
		'https://bitbucket.org/trove4j/trove/downloads'\
		'https://github.com/google/guava' \
		'https://github.com/owlcs/owlapi' \
		>$(BASEDIR)/lib/readme.txt
	@printf '\nNOTE:\n\t%s\n\t%s\n' \
		'Per default $(BASEDIR)/lib/native' \
		'contains JNI libs for Linux and MacOSX only!'

# If one would add haddocs as well, add
#	-m 0755 -d $(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(DOC_DIR)/html/
#	-m 0644 docs/* $(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(DOC_DIR)/html/
install-common: docs install-owl-tools
	$(INSTALL) -m 0755 -d \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)/hets-isa-tools \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)/hets-maude-lib \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(DIST_LATEX)/hets \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(DOC_DIR)
	$(INSTALL) -m 0644 magic/hets.magic utils/hetcasl.sty \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)
	$(INSTALL) -m 0755 Isabelle/export/export.sh \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)/hets-isa-tools/
	$(INSTALL) -m 0644 Isabelle/export/export_helper.ml \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)/hets-isa-tools/
	$(INSTALL) -m 0644 Maude/hets.prj Maude/*maude \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(HETS_DIR)/hets-maude-lib/
	$(INSTALL) -m 0644 doc/*.pdf \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(DOC_DIR)/
	BACK=`printf '$(DIST_LATEX)/hets' | ${SED} -e 's/[^/]\{1,\}/../g'` ; \
	ln -sf $${BACK}/$(HETS_DIR)/hetcasl.sty \
		$(DESTDIR)$(SUBDIR_common)$(PREFIX)/$(DIST_LATEX)/hets/hetcasl.sty
	$(info $(EOL)If TeX is installed, remember to re-run texhash!$(EOL)$(EOL))


%.bin:
	$(MAKE) $*-opt

# for now install-{common,hets,hets_server} are supported, only.
install-%: IDIR = $(DESTDIR)$(SUBDIR_$*)$(PREFIX)
install-%: %.bin
	$(INSTALL) -m 0755 -d \
		$(IDIR)/bin \
		$(IDIR)/$(HETS_DIR) \
		$(IDIR)/$(MAN_DIR)
	$(SED) -e "s,@CLIENT_BASEDIR@,$(PREFIX)," debian/hets_script \
		>$(IDIR)/bin/$(subst _,-,$*)
	chmod 0755 $(IDIR)/bin/$(subst _,-,$*)
	ln $< $(IDIR)/$(HETS_DIR)/$(subst _,-,$*) 2>/dev/null || \
		{ cp -f $< $(IDIR)/$(HETS_DIR)/$(subst _,-,$*) || true ; }
	chmod 0755 $(IDIR)/$(HETS_DIR)/$(subst _,-,$*)
	[ $* = 'hets' ] && RMSECT='SERVER' || RMSECT='DESKTOP' ; \
		$(SED) -e "/@S$${RMSECT}@/,/@E$${RMSECT}@/ d" debian/hets.1 \
			>$(IDIR)/$(MAN_DIR)/$(subst _,-,$*).1
	[ "$(OSNAME)" = 'SunOS' ] || ${SED} -i -e '/@SSOLARIS@/,/@ESOLARIS@/ d' \
		$(IDIR)/$(MAN_DIR)/$(subst _,-,$*).1

install: install-hets install-hets_server install-common install-owl-tools

############################################################################
# DEBIAN rules
############################################################################
build-indep: jars docs

build-arch: $(STACK_TARGET) hets.bin hets_server.bin

build: build-indep build-arch

# For PPA source packages we submit a platform specific changelog via
# *.debian.tar.xz, for local packages we generate it on demand.
CHANGELOG := $(shell [ -f debian/changelog ] && \
	printf 'debian/changelog' || printf 'debian/changelog.tmp')

# See Versioning in ./README
# NOTE: The dash crap sucks! So make sure, we have a ksh93 or bash set as SHELL!
#       We assume only the 2nd rev num might be padded with a single '0'
#       to avoid more clutter.
debian/changelog.tmp: debian/control
	[[ -e debian/control.0 ]] || cp -p debian/control debian/control.0 ; \
	cp -p debian/control.0 debian/control ; \
	echo "# HC_OPTS='$(HC_OPTS)'" >> debian/control ; \
	[[ "$(HC_OPTS)" =~ -DMYSQL ]] || \
		$(SED) -i -e 's/libmysqlclient20, //' debian/control ; \
	[[ ! "$(HC_OPTS)" =~ -DNO_WGET ]] || \
		$(SED) -i -e 's/wget, //' debian/control
	@SRCPKG=`grep ^Source: debian/control |awk '{ print $$2 ; }'` ; \
	if [ -z "${FULL_DEBVERS}" ]; then \
		LSB=`lsb_release -rs`; A="$${LSB%.*}"; B="$${LSB#*.}"; B="$${B##0}"; \
		FULL_DEBVERS="$(HETS_VERSION).1-1.$${A}.$${B}.1" ; \
		printf "\nUsing '$${FULL_DEBVERS}' as new version.\n\n" ; \
	fi ; \
	[ -z "$${REL_NAME}" ] && REL_NAME=`lsb_release -cs` ; \
	[ -z "$${GPG_NAME}" ] && GPG_NAME='Foo Bar' ; \
	[ -z "$${GPG_EMAIL}" ] && GPG_EMAIL='foo.bar@do.main' ; \
	printf "%s (%s) %s; urgency=low\n\n  %s\n\n -- %s <%s>  %s\n" "$${SRCPKG}" \
		"$${FULL_DEBVERS}" "$${REL_NAME}" \
		"* Initial release, automatically generated." \
		"$${GPG_NAME}" "$${GPG_EMAIL}" "`date -R`" \
		>debian/changelog.tmp

# NOTE: dpkg-gencontrol is not POSIX conform wrt. arg processing!
binary-indep: build-indep install-common $(CHANGELOG)
	-@[ "$${USERNAME}" != 'root' -o -z "$${FAKEROOTKEY}" ] && \
		printf '\nWARNING: The $<  target should be called using fakeroot!\n\n'
	$(INSTALL) -m 0755 -d $(DESTDIR)$(SUBDIR_common)/DEBIAN
	dpkg-gencontrol -P$(DESTDIR)$(SUBDIR_common) -phets-common \
		-l$(CHANGELOG)
	dpkg-deb -Z xz -b $(DESTDIR)$(SUBDIR_common) ../hets-A.deb
	dpkg-name -o ../hets-A.deb

binary-arch: build-arch install-hets install-hets_server $(CHANGELOG)
	-@[ "$${USERNAME}" != 'root' -o -z "$${FAKEROOTKEY}" ] && \
		printf '\nWARNING: The $<  target should be called using fakeroot!\n\n'
	$(INSTALL) -m 0755 -d \
		$(DESTDIR)$(SUBDIR_hets)/DEBIAN \
		$(DESTDIR)$(SUBDIR_hets_server)/DEBIAN
	dpkg-gencontrol -P$(DESTDIR)$(SUBDIR_hets) -phets-desktop \
		-l$(CHANGELOG)
	dpkg-deb -Z xz -b $(DESTDIR)$(SUBDIR_hets) ../hets-B.deb
	dpkg-gencontrol -P$(DESTDIR)$(SUBDIR_hets_server) -phets-server \
		-l$(CHANGELOG)
	dpkg-deb -Z xz -b $(DESTDIR)$(SUBDIR_hets_server) ../hets-C.deb
	dpkg-name -o ../hets-B.deb ../hets-C.deb

# Make sure debian/changelog exists, since dpkg-buildpackage runs finally a
# "dpkg-genchanges -b -m'...' >../${fullPkgName}.changes"
binary: binary-indep binary-arch
	@[ -f debian/changelog ] || ln -s changelog.tmp debian/changelog

# vim: ts=4 sw=4 filetype=make
