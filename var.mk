# to be included by Makefile

SHELL := $(shell [ -x /bin/ksh93 ] && echo '/bin/ksh93' || echo '/bin/bash' )
OSNAME := $(shell uname -s)
OSVERS := $(shell uname -v 2>/dev/null)

# Strip off the longest prefix ending with '-' incl. of arg $1, split remaining
# string by '.' and calculate 1.000.000 * ${major} + 1.000 * ${minor} + ${tiny)
# what makes comparing version numbers much easier. If any part in the version
# string is not a number, it gets replaced by '0'.
# This macro requires features found in shells like ksh93 or bash.
version = $(shell X="$(1)"; X="$${X\#\#*-}"; A=( $${X//./ } 0 0 0 ); \
	A=( $$( printf "%d %d %d" "$${A[0]}" "$${A[1]}" "$${A[2]}" )); \
	echo $$(( $${A[0]} * 1000000 + $${A[1]} * 1000 + $${A[2]} )) \
)

# If stack exists, use it. Otherwise skip it and use the system GHC.
STACK ?= $(shell command -v stack 2> /dev/null)
STACK_EXEC :=
STACK_TARGET :=
STACK_UPGRADE_TARGET :=
STACK_DEPENDENCIES_FLAGS :=
ifneq ($(STACK),)
    STACK_EXEC := $(STACK) exec --
    # Upgrade Haskell-Stack if the version requirement of 1.4.0 is not met
    STACK_VERSION := $(call version, $(shell stack --numeric-version))
    STACK_TARGET := stack
    STACK_UPGRADE_TARGET := \
		$(shell [ $(STACK_VERSION) -lt 1004000 ] && echo 'stack_upgrade' )

    ifeq "$(OSNAME)" "Darwin"
        STACK_DEPENDENCIES_FLAGS := --flag gtk:have-quartz-gtk
    endif
endif

## check-programatica convenience target helper vars:
# The URL of the programatica source archive to download if missing. It must be
# a gzippid tar archive, which can be get using wget!
# Don't quote! Space and other shell metcharacters are not allowed!
PROGRAMATICA_SRC_URL ?= \
	http://theo.cs.uni-magdeburg.de/downloads/hets/src/programatica-1.0.0.5.tar.gz
# As an alternative, if you have a local copy of the programatica source
# archive to use.
# Don't quote! Space and other shell metcharacters are not allowed!
PROGRAMATICA_SRC_FILE ?= \
	/data/src/develop/programatica-1.0.0.5.tar.gz
# The local file gets tried first, and if not usable the remote on gets fetched.
# If both are unset or set to an empty string, programatica support is skipped.

# We assume ghc 7+
GHCVERSION := $(call version, $(shell $(STACK_EXEC) ghc --numeric-version))
GHCRTSOPTS := $(shell [ $(GHCVERSION) -ge 7000000 ] && echo '-rtsopts')

ifneq ($(findstring SunOS, $(OSNAME)),)
  TAR = gtar
  PATCH = gpatch
    ifneq ($(findstring Generic, $(OSVERS)),)
      SUNRUNPATH = -optl-R/opt/csw/lib
      FIXED_GLADE = 0
    else
      FIXED_GLADE = 1
    endif
else
  TAR = tar
  PATCH = patch
endif

HC = $(STACK_EXEC) ghc -optl-s -XTemplateHaskell -threaded $(GHCRTSOPTS)
# Compile on all CPU cores in parallel if GHC >= 8.0 is used.
HC += $(shell [ $(GHCVERSION) -ge 8000000 ] && echo '-j')

HCPKG := $(STACK_EXEC) ghc-pkg $(GHC_PKG_FLAGS)

HAXMLVERSION := $(call version, $(shell $(HCPKG) latest HaXml))
HAXML_PACKAGE := $(shell [ $(HAXMLVERSION) -ge 1020000 ] && echo '-DHAXML')
HAXML_PACKAGE_COMPAT := \
	$(shell [ $(HAXMLVERSION) -lt 1021000 ] && echo '-DHAXML_COMPAT')

TARVERSION := $(call version, $(shell $(HCPKG) latest tar))
TAR_PACKAGE := $(shell [ $(TARVERSION) -gt 0 ] && echo '-DTAR_PACKAGE')

UNIXVERSION := $(call version, $(shell $(HCPKG) latest unix))
UNIX_PACKAGE := $(shell [ $(UNIXVERSION) -ge 2000000 ] && echo '-DUNIX')

GTKVERSION := $(call version, $(shell $(HCPKG) latest gtk))
GTK_PACKAGE := \
	$(shell [ $(GTKVERSION) -ge 12000 ] && echo '-DGTKGLADE $(SUNRUNPATH)')
GTK_PACKAGE += $(shell [ $(GTKVERSION) -lt 13000 ] && \
	[ $(FIXED_GLADE) = '0' ] && echo '-DGTK12')

HASKELINEVERSION := $(call version, $(shell $(HCPKG) latest haskeline))
HASKELINE_PACKAGE := \
	$(shell [ $(HASKELINEVERSION) -ge 6000 ] && echo '-DHASKELINE')

HEXPATVERSION := $(call version, $(shell $(HCPKG) latest hexpat))
HEXPAT_PACKAGE := $(shell [ $(HEXPATVERSION) -gt 0 ] && echo '-DHEXPAT')

HTTPVERSION = $(call version, $(shell $(HCPKG) latest HTTP))
HTTP_PACKAGE = $(shell [ $(HTTPVERSION) -lt 4000000000 ] && echo '-DNOHTTP')

HTTPCVERSION := $(call version, $(shell $(HCPKG) latest http-client))
WGET := $(shell [ $(HTTPCVERSION) -ge 5007 ] && echo '-DNO_WGET' )

UNIVERSION := $(call version, $(shell $(HCPKG) latest uni-uDrawGraph))
UNI_PACKAGE := $(shell [ $(UNIVERSION) -ge 2000000 ] && echo '-DUNI_PACKAGE')

PFE_SETUP_FILE := programatica/tools/Setup.hs
# If programatica src, i.e. Setup.hs et. al. is there ...
PFE_SETUP := $(shell ls -1 $(PFE_SETUP_FILE) 2>/dev/null )
# check for haskell programatica module ...
PROGRAMATICAVERSION := $(call version, \
	$(shell [ -n "$(PFE_SETUP)" ] && $(HCPKG) latest programatica))
PFE_FLAGS := $(shell [ $(PROGRAMATICAVERSION) -ge 1000000 ] && \
	echo '-package programatica -DPROGRAMATICA')

WARPVERSION := $(call version, $(shell $(HCPKG) latest warp))
HTTPTYPESVERSION := $(call version, $(shell $(HCPKG) latest http-types))
# warp ensures by itself, that it is linked against the proper wai package. So
# no need to check by ourselves.
SERVER_FLAG := $(shell [ $(WARPVERSION) -ge 1000000 ] && echo '-DSERVER')
SERVER_FLAG += $(shell [ $(WARPVERSION) -ge 3000000 ] && echo '-DWARP3')
SERVER_FLAG += $(shell [ $(WARPVERSION) -lt 2000000 ] && \
	echo '-DWARP1 ' && [ $(HTTPTYPESVERSION) -ge 9000 ] && echo '-DHTTPTYPES')

ifneq ($(strip $(UNI_PACKAGE)),)
  ifeq ($(strip $(HTTP_PACKAGE)),)
  TESTTARGETFILES += SoftFOL/tests/CMDL_tests.hs
  endif
endif

HC_OPTS_WITHOUTGTK = $(PARSEC_FLAG) \
  $(TIME_PACKAGE) $(TAR_PACKAGE) $(HTTP_PACKAGE) $(WGET) $(UNIX_PACKAGE) \
  $(UNI_PACKAGE) $(HASKELINE_PACKAGE) $(HEXPAT_PACKAGE) \
  $(PFE_FLAGS) $(SERVER_FLAG) $(HAXML_PACKAGE) $(HAXML_PACKAGE_COMPAT) \
  -DRDFLOGIC -DCASLEXTENSIONS

# for profiling (or a minimal hets) comment out the previous two package lines
# and the $(GTK_PACKAGE) below

HC_OPTS = $(HC_OPTS_WITHOUTGTK) $(GTK_PACKAGE)
