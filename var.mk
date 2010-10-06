# to be include by Makefile

HC = ghc -optl-s -XTemplateHaskell
HCPKG = ghc-pkg

TIMEVERSION = $(shell $(HCPKG) latest time)
ifneq ($(findstring time-1.1.2, $(TIMEVERSION)),)
TIME_PACKAGE = -DTIME_WITHOUT_TYPEABLE
endif

TARVERSION = $(shell $(HCPKG) field tar version)
ifneq ($(findstring 0.3, $(TARVERSION)),)
TAR_PACKAGE = -DTAR_PACKAGE
endif

UNIXVERSION = $(shell $(HCPKG) field unix version)
ifneq ($(findstring 2.3, $(UNIXVERSION)),)
UNIX_PACKAGE = -DUNIX
endif
ifneq ($(findstring 2.4, $(UNIXVERSION)),)
UNIX_PACKAGE = -DUNIX
endif

GLADEVERSION = $(shell $(HCPKG) field glade version)
ifneq ($(findstring 0.1, $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE
endif

HASKELINEVERSION = $(shell $(HCPKG) field haskeline version)
ifneq ($(findstring 0.6, $(HASKELINEVERSION)),)
HASKELINE_PACKAGE = -DHASKELINE
endif

HEXPATVERSION = $(shell $(HCPKG) field hexpat exposed)
ifneq ($(findstring True, $(HEXPATVERSION)),)
HEXPAT_PACKAGE = -DHEXPAT
else
 XMLVERSION = $(shell $(HCPKG) list xml-1.3.7 --simple-output)
 ifneq ($(findstring xml, $(XMLVERSION)),)
  XMLEXPOSED = $(shell $(HCPKG) field xml-1.3.7 exposed)
  ifneq ($(findstring True, $(XMLEXPOSED)),)
   XMLBYTESTRING_PACKAGE = -DXMLBS
  endif
 endif
endif

HTTPVERSION = $(shell $(HCPKG) field HTTP version)
ifneq ($(findstring 4000.0., $(HTTPVERSION)),)
else
HTTP_PACKAGE = -DNOMATHSERVER
endif

UNIVERSION = $(shell $(HCPKG) field uni-uDrawGraph version)
ifneq ($(findstring 2., $(UNIVERSION)),)
UNI_PACKAGE = -DUNI_PACKAGE
endif

PROGRAMATICAVERSION = $(shell $(HCPKG) field programatica version)
ifneq ($(findstring 1.0, $(PROGRAMATICAVERSION)),)
PFE_FLAGS = -package programatica -DPROGRAMATICA
endif

WAIVERSION = $(shell $(HCPKG) field wai-extra version)
ifneq ($(findstring 0.2., $(WAIVERSION)),)
SERVER_FLAG = -DSERVER
endif


ifneq ($(strip $(UNI_PACKAGE)),)
TESTTARGETFILES += Taxonomy/taxonomyTool.hs OWL/OWLParser.hs \
    Taxonomy/taxonomyTool.hs SoftFOL/tests/CMDL_tests.hs
endif

HC_OPTS_WITHOUTGLADE = -threaded \
  $(TIME_PACKAGE) $(TAR_PACKAGE) $(HTTP_PACKAGE) $(UNIX_PACKAGE) \
  $(UNI_PACKAGE) $(HASKELINE_PACKAGE) $(HEXPAT_PACKAGE) \
  $(XMLBYTESTRING_PACKAGE) $(PFE_FLAGS) $(SERVER_FLAG) \
  -DCASLEXTENSIONS

# for profiling (or a minimal hets) comment out the previous two package lines
# and the $(GLADE_PACKAGE) below

HC_OPTS = $(HC_OPTS_WITHOUTGLADE) $(GLADE_PACKAGE)
