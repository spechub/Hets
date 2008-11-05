# to be include by Makefile

HC = ghc
HCPKG = ghc-pkg

TABULARVERSION = $(shell $(HCPKG) field tabular version)
ifneq ($(findstring 0.1, $(TABULARVERSION)),)
TABULAR_PACKAGE = -DTABULAR_PACKAGE
endif

HAXMLVERSION = $(shell $(HCPKG) field HaXml version)
ifneq ($(findstring 1.13., $(HAXMLVERSION)),)
HAXML_PACKAGE = -DHAXML_PACKAGE
endif

GLADEVERSION = $(shell $(HCPKG) field glade version)
ifneq ($(findstring 0.9.1, $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE
endif

SHELLACVERSION = $(shell $(HCPKG) field Shellac-compatline version)
ifneq ($(findstring 0.9, $(SHELLACVERSION)),)
SHELLAC_PACKAGE = -DSHELLAC
endif

HXTFILTERVERSION = $(shell $(HCPKG) field hxt-filter version)
ifneq ($(findstring 8., $(HXTFILTERVERSION)),)
HXTFILTER_PACKAGE = -DHXTFILTER
else
NOMATHSERVER = -DNOMATHSERVER
endif

UNIVERSION = $(shell $(HCPKG) field uni-uDrawGraph version)
ifneq ($(findstring 2., $(UNIVERSION)),)
UNI_PACKAGE= -DUNI_PACKAGE
endif

PROGRAMATICAVERSION = $(shell $(HCPKG) field programatica version)
ifneq ($(findstring 1.0, $(PROGRAMATICAVERSION)),)
PFE_FLAGS = -package programatica -DPROGRAMATICA
endif

ifeq ($(strip $(UNI_PACKAGE)),)
UNI_PACKAGE_CONF = $(wildcard ../uni/uni-package.conf)
ifneq ($(strip $(UNI_PACKAGE_CONF)),)
UNI_PACKAGE = -package-conf $(UNI_PACKAGE_CONF) -DUNI_PACKAGE

# some modules from uni for haddock
# if uni/server is included also HaXml sources are needed
uni_dirs = ../uni/davinci ../uni/graphs ../uni/events \
    ../uni/reactor ../uni/util ../uni/posixutil

uni_sources = $(wildcard $(addsuffix /haddock/*.hs, $(uni_dirs))) \
    $(wildcard ../uni/htk/haddock/*/*.hs)
endif
TESTTARGETFILES += Taxonomy/taxonomyTool.hs OWL/OWLParser.hs \
    Taxonomy/taxonomyTool.hs SoftFOL/tests/CMDL_tests.hs
endif

HC_OPTS = -threaded -fglasgow-exts -fallow-overlapping-instances \
  $(HAXML_PACKAGE) $(UNI_PACKAGE) $(SHELLAC_PACKAGE) $(HXTFILTER_PACKAGE) \
  $(PFE_FLAGS) $(GLADE_PACKAGE) $(TABULAR_PACKAGE) $(NOMATHSERVER) \
  -DCASLEXTENSIONS
