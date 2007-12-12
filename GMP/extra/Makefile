all:	racer istest lwb gmlgen

racer:
	ghc --make -i../.. ToRacer.hs -o toRacer

istest:
	ghc --make -i../.. Tester4IneqSolv.hs -o isTester

lwb:
	ghc --make -i../.. LWBParser.hs -o lwbParser

gmlgen:
	ghc --make -i../.. TestGenGML.hs -o gmlTestGen

clean:
	rm *.hi *.o; cd ..; make clean

distclean:
	rm lwbParser toRacer isTester gmlTestGen *~;
	make clean
