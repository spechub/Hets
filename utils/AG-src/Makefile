# $Id$

SOURCES = $(wildcard *.hs)
GHC = ghc
GHCFLAGS = -fglasgow-exts -package util -fallow-undecidable-instances

ag: $(SOURCES)
	ghc $(GHCFLAGS) --make Ag.hs -o ag

clean:
	$(RM) *.hi *.hi.bak *.o

distclean: clean
	$(RM) ag
