# Makefile
# $Id$
# Author: (c) Klaus Luettich, Christian Maeder, Uni Bremen 2002-2009

# This Makefile will compile the hets system and provides also
# targets for test programs during implementation phases.

# !!! Note: This makefile is written for GNU make !!!
#           (gmake on solaris)

all: hets

include var.mk

# the 'replacing spaces' example was taken from the (GNU) Make info manual
empty =
space = $(empty) $(empty)

DRIFT_ENV = DERIVEPATH=$(subst $(space),:,$(PFE_PATHS))

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
    SoftFOL ConstraintCASL Propositional RelationalScheme EVT VSE OMDoc DFOL \
    LF Framework Maude ExtModal CommonLogic CSL QBF Adl HolLight Fpl THF \
    FreeCAD OWL2 RDF CSMOF QVTR

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

PFE_TOOLDIR = $(wildcard programatica/tools)
ifneq ($(strip $(PFE_TOOLDIR)),)
PFE_DIRS = base/AST base/TI base/parse2 base/parse2/Lexer base/parse2/Parser \
    base/parse2/LexerGen base/parse2/LexerSpec base/tests/HbcLibraries \
    base/pretty base/syntax base/lib base/lib/Monads base/Modules base/defs \
    base/transforms base/transforms/Deriving property \
    property/syntax property/AST property/transforms \
    property/TI property/defs property/parse2 property/parse2/Parser

PFE_PATHS = $(addprefix $(PFE_TOOLDIR)/, $(PFE_DIRS))

logics += Haskell
derived_sources += Haskell/PreludeString.hs

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
	$(GENRULECALL) -r Typeable -i Data.Typeable -i Haskell.BaseATC \
  -o $@ $(Haskell_files)

hs_der_files += $(hs_clean_files)
ifneq ($(strip $(PFE_FLAGS)),)
TESTDIRS += ToHaskell
TESTTARGETFILES += Haskell/hana.hs Haskell/h2h.hs Haskell/h2hf.hs
endif
else
# unset this variable from var.mk because the programatica sources
# are needed to created our sources!
PFE_FLAGS =
endif
# end of programatica stuff

TESTTARGETS = $(subst .hs,,$(TESTTARGETFILES))

GHCVERSION = $(shell ghc --numeric-version)
ifneq ($(findstring 12, $(GHCVERSION)),)
NO_BIND_WARNING = -fno-warn-unused-do-bind
endif

ifneq ($(findstring 7, $(GHCVERSION)),)
NO_BIND_WARNING = -fno-warn-unused-do-bind
endif

HC_WARN = -Wall -fwarn-tabs \
  -fwarn-unrecognised-pragmas -fno-warn-orphans $(NO_BIND_WARNING)

# uncomment HC_PROF for profiling (and comment out packages in var.mk)
# call resulting binary with a final +RTS -p to get a file <binary>.prof
# HC_PROF = -prof -auto-all -osuf p_o +RTS -K100m -RTS

ifneq ($(findstring -O, $(CFLAGS)),)
HC_DEBIAN_OPT=-O
endif

HC_OPTS += $(HC_WARN) $(HC_PROF) $(HC_DEBIAN_OPT)
# -ddump-minimal-imports
# uncomment the above line to generate .imports files for displayDependencyGraph

# files generated by DriFT
drifted_files = Common/AS_Annotation.hs \
    CASL/AS_Basic_CASL.hs Modal/AS_Modal.hs Hybrid/AS_Hybrid.hs TopHybrid/AS_TopHybrid.hs  \
    Syntax/AS_Structured.hs Syntax/AS_Architecture.hs Syntax/AS_Library.hs \
    Propositional/AS_BASIC_Propositional.hs \
    CoCASL/AS_CoCASL.hs COL/AS_COL.hs \
    CASL_DL/AS_CASL_DL.hs THF/As.hs \
    CspCASL/AS_CspCASL_Process.hs CspCASL/AS_CspCASL.hs \
    RelationalScheme/AS.hs EVT/AS.hs ATC/Grothendieck.hs \
    ExtModal/AS_ExtModal.hs QBF/AS_BASIC_QBF.hs \
    CommonLogic/AS_CommonLogic.hs Fpl/As.hs \
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
  OWL2/Profiles.hs

RDF_files = RDF/AS.hs OWL2/AS.hs RDF/Symbols.hs RDF/Sign.hs RDF/Morphism.hs \
  RDF/Sublogic.hs

CSMOF_files = CSMOF/As.hs CSMOF/Sign.hs

QVTR_files = QVTR/As.hs QVTR/Sign.hs

EVT_files = EVT/AS.hs EVT/Sign.hs 

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

EVT/ATC_EVT.der.hs: $(EVT_files) $(GENRULES)
	$(GENRULECALL) -i ATC.GlobalAnnotations -o $@ $(EVT_files)

# all ATC .der.hs files for all logics
atc_logic_files = $(foreach logic, $(logics), $(logic)/ATC_$(logic).der.hs)

generated_rule_files = $(atc_der_files) $(atc_logic_files)

# a rule to create all .der.hs files
genRules: $(generated_rule_files)

# the final ATC target files created by DriFT
gendrifted_files = $(patsubst %.der.hs, %.hs, $(generated_rule_files))

# all sources that need to be created before ghc can be called
derived_sources += $(drifted_files) Driver/Version.hs $(hs_der_files)

####################################################################
### targets

.NOTPARALLEL : genRules

.PHONY : all hets-opt hets-optimized clean o_clean clean_pretty \
    real_clean bin_clean distclean annos checkversion \
    check capa hacapa h2h h2hf showKP clean_genRules genRules \
    count doc fromKif derivedSources release cgi ghci build callghc rev.txt

.FORCE :

.SECONDARY : %.hs %.d $(generated_rule_files)

# dummy target to force ghc invocation
callghc:

hets-opt:
	$(MAKE) distclean
	$(MAKE) derivedSources
	$(MAKE) clean
	$(MAKE) hets-optimized

# the variant without GUI
hets-server: HASKELINE_PACKAGE =
hets-server: GLADE_PACKAGE =
hets-server: UNI_PACKAGE =
hets-server: $(derived_sources)
	$(HC) --make -O -o hets-server hets.hs $(HC_OPTS)

hets-optimized: $(derived_sources)
	$(HC) --make -O -o hets hets.hs $(HC_OPTS)

cgi:
	$(MAKE) distclean
	$(MAKE) derivedSources
	$(MAKE) clean
	$(MAKE) hets.cgi

hets.cgi: GUI/hets_cgi.hs
	ghc --make GUI/hets_cgi.hs -o $@ $(HC_OPTS) -O

# Documentation via haddock
doc: docs/index.html

HADDOCK_INTERFACES = $(shell find `ghc --print-libdir`/../.. -name \*.haddock)

HAD_INTS = $(foreach file, $(HADDOCK_INTERFACES),\
 -i http://hackage.haskell.org/packages/archive/$(basename $(notdir $(file)))/latest/doc/html,$(file))

HADDOCK_OPTS = $(addprefix --optghc=, $(HC_OPTS))
docs/index.html:
	$(RM) -r docs
	mkdir docs
	$(HADDOCK) -o docs -h -s ../%F $(HAD_INTS) \
            -t 'Hets - the Heterogeneous Tool Set' \
            -p Hets-Haddock-Prologue.txt $(HADDOCK_OPTS) \
             $(filter-out Scratch.hs, $(wildcard *.hs))

derivedSources: $(derived_sources)

deps: .FORCE $(derived_sources)
	$(HC) -M -dep-makefile Makefile.deps hets.hs $(HC_OPTS)
	cat Makefile.deps | grep .hs | awk '{print $$3}' > deps

compile_in_steps: deps
	cat deps | xargs -L 200 $(HC) --make -odir=.objs $(HC_OPTS)

$(DRIFT): $(DRIFT_deps)
	(cd utils/DrIFT-src; $(HC) --make DrIFT.hs -o ../DrIFT)

$(DTD2HS): $(DTD2HS_deps) utils/DtdToHaskell-src/DtdToHaskell.hs
	mkdir -p utils/DtdToHaskell-src/DtdToHaskell
	cp -f $(DTD2HS_deps) utils/DtdToHaskell-src/DtdToHaskell
	$(HC) --make -iutils/DtdToHaskell-src \
            utils/DtdToHaskell-src/DtdToHaskell.hs -o $@ $(HC_OPTS)

Isabelle/IsaExport.hs: $(DTD2HS) Isabelle/IsaExport.dtd
	($(DTD2HS) Isabelle/IsaExport.dtd Isabelle/IsaExport.hs Isabelle.)

$(GENRULES): $(DRIFT) $(GENERATERULES_deps)
	(cd utils/GenerateRules; \
            $(HC) --make -i../DrIFT-src -i../.. $(HC_WARN) \
                GenerateRules.hs -o ../genRules)

utils/appendHaskellPreludeString: utils/appendHaskellPreludeString.hs
	$(HC) --make -o $@ $<

# release management
release:
	$(RM) -r Hets
	git clone --depth=50 $(HETSBRANCH) https://github.com/spechub/Hets
	(cd Hets; $(MAKE) derivedSources; $(MAKE) clean; \
            cp Makefile Makefile.orig; \
            cp ReleaseMakefile Makefile; \
            ./clean.sh; \
            $(RM) clean.*; utils/replaceAllHeaders.sh)
	$(TAR) cf Hets.tar Hets

# Common/LaTeX_maps.hs generation
utils/genItCorrections: $(GENITCORRECTIONS_deps)
	$(HC) --make -o $@ $<

pretty/LaTeX_maps.hs: utils/words.pl utils/genItCorrections \
    pretty/words.input pretty/fonts.input pretty/width-table.tex.templ
	@echo -n "Generating pretty/LaTeX_maps.hs ... "
	@(cd pretty >/dev/null; $(PERL) ../utils/words.pl > words.pl.log)
	@(cd pretty >/dev/null; ../utils/genItCorrections \
            gen_it_characters gen_it_words >> LaTeX_maps.hs)
	@echo "ready"
	@echo "please copy the file manually to Common"

### clean up
clean_genRules:
	$(RM) $(generated_rule_files) $(gendrifted_files) \
            $(hs_clean_files)

clean: bin_clean o_clean clean_pretty clean_javastuff

### removes all *.o, *.hi and *.p_o files in all subdirectories
o_clean:
	find . -name \*.o -o -name \*.hi -o -name \*.p_o \
        -o -name \*.dyn_hi -o -name \*.dyn_o \
        -o -name \*.exe -o -name \*.exe.manifest | xargs $(RM)

### remove binaries
bin_clean:
	$(RM) hets
	$(RM) hets.cgi
	$(RM) hets-server
	$(RM) $(TESTTARGETS)

clean_pretty:
	$(RM) pretty/*.c.* pretty/*.h.* pretty/gen_it_* \
               pretty/generated_words.tex
	$(RM) test/*/*.{thy,pp.het,pp.tex,th,dfg.c,xml,log,dvi,aux,sty}
	$(RM) test/*/log
	$(RM) ToHaskell/test/*.{out,output}
	$(RM) */test/temp*
	$(RM) doc/UserGuide.{log,aux,bbl,blg,out,pdf}

clean_javastuff:
	$(RM) OWL2/*.jar OWL2/java/lib/*.jar
	$(RM) -r OWL2/java/build OWL2/lib

### additionally removes the library files
real_clean: clean

### additionally removes generated files not in the repository tree
distclean: clean clean_genRules
	$(RM) $(derived_sources)
	$(RM) utils/appendHaskellPreludeString
	$(RM) utils/DrIFT utils/genRules
	$(RM) $(DTD2HS)
	$(RM) -r utils/DtdToHaskell-src/DtdToHaskell
	$(RM) utils/genItCorrections pretty/LaTeX_maps.hs pretty/words.pl.log
	$(RM) -r docs

### interactive
ghci: $(derived_sources)
	ghci $(HC_OPTS)

### build only, don't link
build: hets.hs
	$(HC) --make -c $< $(HC_OPTS)

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
	$(HC) -O --make -o $@ $< $(HC_OPTS)

### HasCASL to Haskell translation
h2h: Haskell/h2h

### test program to check the known provers
showKP: Comorphisms/test/showKP

### run tests in other directories
check: $(TESTTARGETS)
	for i in $(TESTDIRS); do $(MAKE) -C $$i check; done

## Preparing the version of Hets
Driver/Version.hs: Driver/Version.in version_nr rev.txt
	$(RM) $@
	cp Driver/Version.in $@
	echo "  ++ \"$(shell cat version_nr), $(shell cat rev.txt)\"" >> $@
	chmod 444 $@

rev.txt:
	$(RM) $@
	echo $(shell git log -1 --format=%ct) >> $@

checkversion:

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
%: %.hs callghc
	$(HC) --make -o $@ $< $(HC_OPTS)

## rule for DrIFT
%.hs: %.der.hs $(DRIFT)
	$(RM) $@
	($(DRIFT_ENV); export DERIVEPATH; $(DRIFT) $< > $@)
	chmod 444 $@

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

## Rule to generate hs files from glade files. Needed for GTK
%.hs: %.glade utils/appendHaskellPreludeString \
  GUI/Glade/Template.append.hs
	b=`basename $< .glade`; \
    cat GUI/Glade/Template.append.hs | sed "s/\%s/$$b/" | \
    utils/appendHaskellPreludeString $< > $@

# directory for installers
INSTALLER_DIR = ../installers

ifeq ($(strip $(HETS_VERSION)),)
HETS_VERSION := `cat version_nr`
# or `date +%F`
endif

# prepare installer creation
initialize_installer:
	mkdir -p $(INSTALLER_DIR)
	sed "s/^\(HETS_VERSION =\).*/\1$(HETS_VERSION)/" Makefile.installer \
          > $(INSTALLER_DIR)/Makefile
	@echo Please do
	@echo "  -> cd $(INSTALLER_DIR)"
	@echo "  -> make"
	@echo and wait until it is finished

initialize_java:
	ant -q init

java-libs:
	ant -q java-libs

java-files:
	ant -q java-files

java-clean:
	ant -q java-clean

# download dependencies for RDF Jena-api
rdf_java:
	mkdir -p RDF/java/lib
	if [ -f RDF/java/lib/arq-2.8.7.jar ]; then \
		echo "File arq-2.8.7.jar already exists"; \
	else \
		curl -o RDF/java/lib/arq-2.8.7.jar http://repo1.maven.org/maven2/com/hp/hpl/jena/arq/2.8.7/arq-2.8.7.jar; \
	fi
	if [ -f RDF/java/lib/icu4j-3.4.4.jar ]; then \
		echo "File icu4j-3.4.4.jar already exists"; \
	else \
		curl -o RDF/java/lib/icu4j-3.4.4.jar http://repo1.maven.org/maven2/com/ibm/icu/icu4j/3.4.4/icu4j-3.4.4.jar; \
	fi
	if [ -f RDF/java/lib/iri-0.8.jar ]; then \
		echo "File iri-0.8.jar already exists"; \
	else \
		curl -o RDF/java/lib/iri-0.8.jar http://repo1.maven.org/maven2/com/hp/hpl/jena/iri/0.8/iri-0.8.jar; \
	fi
	if [ -f RDF/java/lib/jena-2.6.4.jar ]; then \
		echo "File jena-2.6.4.jar already exists"; \
	else \
		curl -o RDF/java/lib/jena-2.6.4.jar http://repo1.maven.org/maven2/com/hp/hpl/jena/jena/2.6.4/jena-2.6.4.jar; \
	fi
	if [ -f RDF/java/lib/junit-4.5.jar ]; then \
		echo "File junit-4.5.jar already exists"; \
	else \
		curl -o RDF/java/lib/junit-4.5.jar http://repo1.maven.org/maven2/junit/junit/4.5/junit-4.5.jar; \
	fi
	if [ -f RDF/java/lib/log4j-1.2.13.jar ]; then \
		echo "File log4j-1.2.13.jar already exists"; \
	else \
		curl -o RDF/java/lib/log4j-1.2.13.jar http://repo1.maven.org/maven2/log4j/log4j/1.2.13/log4j-1.2.13.jar; \
	fi
	if [ -f RDF/java/lib/lucene-core-2.3.1.jar ]; then \
		echo "File lucene-core-2.3.1.jar already exists"; \
	else \
		curl -o RDF/java/lib/lucene-core-2.3.1.jar http://repo1.maven.org/maven2/org/apache/lucene/lucene-core/2.3.1/lucene-core-2.3.1.jar; \
	fi
	if [ -f RDF/java/lib/slf4j-api-1.5.8.jar ]; then \
		echo "File slf4j-api-1.5.8.jar already exists"; \
	else \
		curl -o RDF/java/lib/slf4j-api-1.5.8.jar http://repo2.maven.org/maven2/org/slf4j/slf4j-api/1.5.8/slf4j-api-1.5.8.jar; \
	fi
	if [ -f RDF/java/lib/slf4j-log4j12-1.5.8.jar ]; then \
		echo "File slf4j-log4j12-1.5.8.jar already exists"; \
	else \
		curl -o RDF/java/lib/slf4j-log4j12-1.5.8.jar http://repo2.maven.org/maven2/org/slf4j/slf4j-log4j12/1.5.8/slf4j-log4j12-1.5.8.jar; \
	fi
	if [ -f RDF/java/lib/stax-api-1.0.1.jar ]; then \
		echo "File stax-api-1.0.1.jar already exists"; \
	else \
		curl -o RDF/java/lib/stax-api-1.0.1.jar http://dist.codehaus.org/stax/jars/stax-api-1.0.1.jar; \
	fi
	if [ -f RDF/java/lib/wstx-asl-3.2.9.jar ]; then \
		echo "File wstx-asl-3.2.9.jar already exists"; \
	else \
		curl -o RDF/java/lib/wstx-asl-3.2.9.jar http://repo1.maven.org/maven2/org/codehaus/woodstox/wstx-asl/3.2.9/wstx-asl-3.2.9.jar; \
	fi
	if [ -f RDF/java/lib/xercesImpl-2.7.1.jar ]; then \
		echo "File xercesImpl-2.7.1.jar already exists"; \
	else \
		curl -o RDF/java/lib/xercesImpl-2.7.1.jar http://mirrors.ibiblio.org/pub/mirrors/maven2/xerces/xercesImpl/2.7.1/xercesImpl-2.7.1.jar; \
	fi

# download rdf4h, unpack and install
rdf4h:
	cabal install http://protempore.net/rdf4h/rdf4h-0.6.1.tar.gz
# DO NOT DELETE: Beginning of Haskell dependencies
CSMOF/CSMOF/As.o : CSMOF/As.hs
CSMOF/CSMOF/Test_As.o : CSMOF/Test_As.hs
CSMOF/CSMOF/Test_As.o : CSMOF/As.hi

#QVTR/QVTR/As.o : QVTR/As.hs
# DO NOT DELETE: End of Haskell dependencies
