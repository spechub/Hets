# to be include by Makefile

GHCVERSION = $(shell ghc --numeric-version)
ifneq ($(findstring 7., $(GHCVERSION)),)
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

HAXMLVERSION = $(shell $(HCPKG) latest HaXml)
ifneq ($(findstring HaXml-1.2, $(HAXMLVERSION)),)
HAXML_PACKAGE = -DHAXML
endif
ifneq ($(findstring HaXml-1.20, $(HAXMLVERSION)),)
HAXML_PACKAGE_COMPAT = -DHAXML_COMPAT
endif

TARVERSION = $(shell $(HCPKG) latest tar)
ifneq ($(findstring 0., $(TARVERSION)),)
TAR_PACKAGE = -DTAR_PACKAGE
endif

UNIXVERSION = $(shell $(HCPKG) latest unix)
ifneq ($(findstring 2., $(UNIXVERSION)),)
UNIX_PACKAGE = -DUNIX
endif

GLADEVERSION = $(shell $(HCPKG) latest glade)
ifneq ($(findstring 0.12, $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE -DGTK12 $(SUNRUNPATH)
endif
ifneq ($(findstring 0.13, $(GLADEVERSION)),)
GLADE_PACKAGE = -DGTKGLADE $(SUNRUNPATH)
endif

HASKELINEVERSION = $(shell $(HCPKG) latest haskeline)
ifneq ($(findstring 0.6, $(HASKELINEVERSION)),)
HASKELINE_PACKAGE = -DHASKELINE
endif
ifneq ($(findstring 0.7, $(HASKELINEVERSION)),)
HASKELINE_PACKAGE = -DHASKELINE
endif

HEXPATVERSION = $(shell $(HCPKG) latest hexpat)
ifneq ($(findstring 0., $(HEXPATVERSION)),)
HEXPAT_PACKAGE = -DHEXPAT
endif

HTTPVERSION = $(shell $(HCPKG) latest HTTP)
ifneq ($(findstring 4000., $(HTTPVERSION)),)
else
HTTP_PACKAGE = -DNOHTTP
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
WARPVERSION = $(shell $(HCPKG) latest warp)
HTTPTYPESVERSION = $(shell $(HCPKG) latest http-types)
ifneq ($(findstring -1., $(WARPVERSION)),)
  ifneq ($(findstring -1., $(WAIEXTVERSION)),)
    ifneq ($(findstring .8, $(HTTPTYPESVERSION)),)
      SERVER_FLAG = -DSERVER -DWARP1
    else
      SERVER_FLAG = -DSERVER -DWARP1 -DHTTPTYPES
    endif
  endif
endif
ifneq ($(findstring -2., $(WARPVERSION)),)
  ifneq ($(findstring -2., $(WAIEXTVERSION)),)
  SERVER_FLAG = -DSERVER
  endif
endif
ifneq ($(findstring -3., $(WARPVERSION)),)
  ifneq ($(findstring -3., $(WAIEXTVERSION)),)
  SERVER_FLAG = -DSERVER -DWARP3
  endif
endif


PARSEC1VERSION = $(shell $(HCPKG) latest parsec1)
ifneq ($(findstring 1.0., $(PARSEC1VERSION)),)
PARSEC_FLAG = -hide-package parsec -package parsec1
endif

ifneq ($(strip $(UNI_PACKAGE)),)
  ifeq ($(strip $(HTTP_PACKAGE)),)
  TESTTARGETFILES += SoftFOL/tests/CMDL_tests.hs
  endif
endif

ifneq ($(findstring Darwin, $(OSBYUNAME)),)
HASKELINE_PACKAGE =
GLADE_PACKAGE =
endif

HC_OPTS_WITHOUTGLADE = $(PARSEC_FLAG) \
  $(TIME_PACKAGE) $(TAR_PACKAGE) $(HTTP_PACKAGE) $(UNIX_PACKAGE) \
  $(UNI_PACKAGE) $(HASKELINE_PACKAGE) $(HEXPAT_PACKAGE) \
  $(PFE_FLAGS) $(SERVER_FLAG) $(HAXML_PACKAGE) $(HAXML_PACKAGE_COMPAT) \
  -DRDFLOGIC -DCASLEXTENSIONS

# for profiling (or a minimal hets) comment out the previous two package lines
# and the $(GLADE_PACKAGE) below

HC_OPTS = $(HC_OPTS_WITHOUTGLADE) $(GLADE_PACKAGE)
