call:
	./ghc-call

racer:
	ghc --make -i.. ToRacer.hs -o toRacer

tester:
	ghc --make -i.. Tester4IneqSolv.hs -o isTester

lwb:
	ghc --make -i.. LWBParser.hs -o lwbParser

clean:
	rm main *.hi *.o

distclean:
	rm main *.hi *.o *~ lwbParser toRacer isTester
