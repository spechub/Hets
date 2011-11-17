# to be include by Makefile

GHCVERSION = $(shell ghc --numeric-version)
ifneq ($(findstring 7., $(GHCVERSION)),)
GHC7OPTS = -fcontext-stack=31
GHC7RTSOPTS = -rtsopts
endif

OSBYUNAME = $(shell uname)
ifneq ($(findstring SunOS, $(OSBYUNAME)),)
TAR = gtar
PATCH = gpatch
SUNRUNPATH = -optl-R/opt/csw/lib
else
TAR = tar
PATCH = patch
endif

HC = ghc -optl-s -XTemplateHaskell -threaded $(GHC7RTSOPTS)

HCPKG = ghc-pkg

TIMEVERSION = $(shell $(HCPKG) latest time)
ifneq ($(findstring time-1.1.2, $(TIMEVERSION)),)
TIME_PACKAGE = -DTIME_WITHOUT_TYPEABLE
endif

TARVERSION = $(shell $(HCPKG) latest tar)
ifneq ($(findstring 0.3, $(TARVERSION)),)
TAR_PACKAGE = -DTAR_PACKAGE
endif

UNIXVERSION = $(shell $(HCPKG) latest unix)
ifneq ($(findstring 2., $(UNIXVERSION)),)
UNIX_PACKAGE = -DUNIX
endif
ifneq ($(findstring 2.4, $(UNIXVERSION)),)
UNIX_PACKAGE = -DUNIX
endif

GLADEVERSION = $(shell $(HCPKG) latest glade)
ifneq ($(findstring 0.1, $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE $(SUNRUNPATH)
endif

HASKELINEVERSION = $(shell $(HCPKG) latest haskeline)
ifneq ($(findstring 0.6, $(HASKELINEVERSION)),)
HASKELINE_PACKAGE = -DHASKELINE
endif

HEXPATVERSION = $(shell $(HCPKG) latest hexpat)
ifneq ($(findstring 0.1, $(HEXPATVERSION)),)
HEXPAT_PACKAGE = -DHEXPAT
endif

HTTPVERSION = $(shell $(HCPKG) latest HTTP)
ifneq ($(findstring 4000., $(HTTPVERSION)),)
else
HTTP_PACKAGE = -DNOMATHSERVER
endif

UNIVERSION = $(shell $(HCPKG) latest uni-uDrawGraph)
ifneq ($(findstring 2., $(UNIVERSION)),)
UNI_PACKAGE = -DUNI_PACKAGE
endif

PROGRAMATICAVERSION = $(shell $(HCPKG) latest programatica)
ifneq ($(findstring 1.0, $(PROGRAMATICAVERSION)),)
PFE_FLAGS = -package programatica -DPROGRAMATICA
endif

WAIEXTVERSION = $(shell $(HCPKG) latest wai-extra)
WAIVERSION = $(shell $(HCPKG) latest wai)
WARPVERSION = $(shell $(HCPKG) latest warp)
ifneq ($(findstring 0.4, $(WARPVERSION)),)
  ifneq ($(findstring 0.4, $(WAIEXTVERSION)),)
  SERVER_FLAG = -DSERVER
  endif
endif
ifneq ($(findstring 0.2, $(WAIEXTVERSION)),)
  ifneq ($(findstring 0.2, $(WAIVERSION)),)
  SERVER_FLAG = -DSERVER -DOLDSERVER
  endif
endif

PARSEC1VERSION = $(shell $(HCPKG) latest parsec1)
ifneq ($(findstring 1.0., $(PARSEC1VERSION)),)
PARSEC_FLAG = -hide-package parsec -package parsec1
endif

ifneq ($(strip $(UNI_PACKAGE)),)
TESTTARGETFILES += Taxonomy/taxonomyTool.hs SoftFOL/tests/CMDL_tests.hs
endif

HC_OPTS_WITHOUTGLADE = $(GHC7OPTS) $(PARSEC_FLAG) \
  $(TIME_PACKAGE) $(TAR_PACKAGE) $(HTTP_PACKAGE) $(UNIX_PACKAGE) \
  $(UNI_PACKAGE) $(HASKELINE_PACKAGE) $(HEXPAT_PACKAGE)\
  $(PFE_FLAGS) $(SERVER_FLAG) \
  -DCASLEXTENSIONS

# for profiling (or a minimal hets) comment out the previous two package lines
# and the $(GLADE_PACKAGE) below

HC_OPTS = $(HC_OPTS_WITHOUTGLADE) $(GLADE_PACKAGE)
