mcc: *.hs
	ghc -o $@ --make Main.hs

clean:
	-rm *.hi *.o mcc

demo: mcc mutex.smv
	./mcc "AG(request -> F status=busy)" < mutex.smv | NuSMV

demo2: mcc formula.txt mutex.smv
	./mcc formula.txt < mutex.smv | NuSMV
