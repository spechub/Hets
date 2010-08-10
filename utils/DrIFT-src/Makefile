# utils/DrIFT-src/Makefile
# $Id$
# Author: Klaus Lüttich
# Year:   2002

# A Makefile to compile DrIFT in a comfortable way for various plattforms.

DrIFT: DrIFT.hs
	ghc -Wall -fno-warn-unused-do-bind --make $<

### clean up
.PHONY : clean
clean:
	rm -f DrIFT *.hi *.o
