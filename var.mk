# to be include by Makefile

HC = ghc -optl-s -XTemplateHaskell
HCPKG = ghc-pkg

TIMEVERSION = $(shell $(HCPKG) field time version)
ifneq ($(findstring 1.1.3, $(TIMEVERSION)),)
TIME_PACKAGE = -DTIME_WITH_TYPEABLE
endif
ifneq ($(findstring 1.1.4, $(TIMEVERSION)),)
TIME_PACKAGE = -DTIME_WITH_TYPEABLE
endif

TARVERSION = $(shell $(HCPKG) field tar version)
ifneq ($(findstring 0.3, $(TARVERSION)),)
TAR_PACKAGE = -DTAR_PACKAGE
endif

TABULARVERSION = $(shell $(HCPKG) field tabular version)
ifneq ($(findstring 0.1, $(TABULARVERSION)),)
TABULAR_PACKAGE = -DTABULAR_PACKAGE
endif

GLADEVERSION = $(shell $(HCPKG) field glade version)
ifneq ($(findstring 0., $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE
endif

SHELLACVERSION = $(shell $(HCPKG) field Shellac-haskeline version)
ifneq ($(findstring 0.2, $(SHELLACVERSION)),)
SHELLAC_PACKAGE = -DSHELLAC
endif

EDITLINEVERSION = $(shell $(HCPKG) field Shellac-editline version)
ifneq ($(findstring 0.9, $(EDITLINEVERSION)),)
EDITLINE_PACKAGE = -DEDITLINE
SHELLAC_PACKAGE = -DSHELLAC
endif

HXTFILTERVERSION = $(shell $(HCPKG) field hxt-filter version)
ifneq ($(findstring 8., $(HXTFILTERVERSION)),)
HXTFILTER_PACKAGE = -DHXTFILTER
endif

UNIVERSION = $(shell $(HCPKG) field uni-uDrawGraph version)
ifneq ($(findstring 2., $(UNIVERSION)),)
UNI_PACKAGE = -DUNI_PACKAGE
endif

PROGRAMATICAVERSION = $(shell $(HCPKG) field programatica version)
ifneq ($(findstring 1.0, $(PROGRAMATICAVERSION)),)
PFE_FLAGS = -package programatica -DPROGRAMATICA
endif

ifneq ($(strip $(UNI_PACKAGE)),)
TESTTARGETFILES += Taxonomy/taxonomyTool.hs OWL/OWLParser.hs \
    Taxonomy/taxonomyTool.hs SoftFOL/tests/CMDL_tests.hs
endif

HC_OPTS_WITHOUTGLADE = -threaded -fglasgow-exts -XOverlappingInstances \
  $(TIME_PACKAGE) $(TAR_PACKAGE) \
  $(UNI_PACKAGE) $(SHELLAC_PACKAGE) $(HXTFILTER_PACKAGE) \
  $(PFE_FLAGS) $(TABULAR_PACKAGE) $(EDITLINE_PACKAGE) -DCASLEXTENSIONS

# for profiling (or a minimal hets) comment out the previous two package lines
# and the $(GLADE_PACKAGE) below

HC_OPTS = $(HC_OPTS_WITHOUTGLADE) $(GLADE_PACKAGE)
