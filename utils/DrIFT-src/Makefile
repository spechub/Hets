# utils/DrIFT-src/Makefile
# $Id$
# Author: Klaus Lüttich
# Year:   2002

# A Makefile to compile DrIFT in a comfortable way for various plattforms.

DrIFT: DrIFT.hs
	ghc -Wall --make $<

### clean up
.PHONY : clean
clean:
	rm -f DrIFT *.hi *.o
