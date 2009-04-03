# to be include by Makefile

HC = ghc -optl-s -XTemplateHaskell -XCPP
HCPKG = ghc-pkg

TARVERSION = $(shell $(HCPKG) field tar version)
ifneq ($(findstring 0.3, $(TARVERSION)),)
TAR_PACKAGE = -DTAR_PACKAGE
endif

TABULARVERSION = $(shell $(HCPKG) field tabular version)
ifneq ($(findstring 0.1, $(TABULARVERSION)),)
TABULAR_PACKAGE = -DTABULAR_PACKAGE
endif

HAXMLVERSION = $(shell $(HCPKG) field HaXml version)
ifneq ($(findstring 1.13., $(HAXMLVERSION)),)
HAXML_PACKAGE = -DHAXML_PACKAGE
endif

GLADEVERSION = $(shell $(HCPKG) field glade version)
ifneq ($(findstring 0., $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE
endif

SHELLACVERSION = $(shell $(HCPKG) field Shellac-compatline version)
ifneq ($(findstring 0.9, $(SHELLACVERSION)),)
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
else
NOMATHSERVER = -DNOMATHSERVER
endif

UNIVERSION = $(shell $(HCPKG) field uni-uDrawGraph version)
ifneq ($(findstring 2., $(UNIVERSION)),)
UNI_PACKAGE = -DUNI_PACKAGE -DUNIVERSION2
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
endif

ifneq ($(strip $(UNI_PACKAGE)),)
TESTTARGETFILES += Taxonomy/taxonomyTool.hs OWL/OWLParser.hs \
    Taxonomy/taxonomyTool.hs SoftFOL/tests/CMDL_tests.hs
endif

HC_OPTS_WITHOUTGLADE = -threaded -fglasgow-exts -XOverlappingInstances \
  $(NOMATHSERVER) $(TAR_PACKAGE) \
  $(HAXML_PACKAGE) $(UNI_PACKAGE) $(SHELLAC_PACKAGE) $(HXTFILTER_PACKAGE) \
  $(PFE_FLAGS) $(TABULAR_PACKAGE) $(EDITLINE_PACKAGE) -DCASLEXTENSIONS

# for profiling (or a minimal hets) comment out the previous two package lines
# and the $(GLADE_PACKAGE) below

HC_OPTS = $(HC_OPTS_WITHOUTGLADE) $(GLADE_PACKAGE)
