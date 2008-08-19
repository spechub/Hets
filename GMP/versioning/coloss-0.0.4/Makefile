clean:
	-rm *~ mySat.hs MySat.hs *.hi *.o a.out 2>/dev/null; exit 0

dist:
	make clean; DIR=`pwd`; BN=`basename $$PWD`; cd ..; tar czf $$BN.tar.gz $$BN
