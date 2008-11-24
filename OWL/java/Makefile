INCLUDES=.:./lib/owlapi-bin.jar:./lib/aterm-java-1.6.jar

TARGET=1.5

JC=javac

world: get compile store install

small-world: compile store install

compile:

	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermFormat.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/ATermFunc.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermObjectRenderer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermRenderer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermStorer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWL2ATerm.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./de/unibremen/informatik/locality/LocalityChecker.java

store:
	jar cmf ./MANIFEST.MF OWL2ATerm.jar org/hets/owl11/atermRender/*.class 
	jar cmf ./MANIFEST-LOCALITY.MF OWLLocality.jar de/unibremen/informatik/locality/*.class

install:
	cp lib/aterm-java-1.6.jar ../lib/
	cp lib/owlapi-bin.jar ../lib/
	cp OWL2ATerm.jar ..
	cp OWLLocality.jar ..

clean: 
	rm -r OWL2ATerm.jar OWLLocality.jar ./org/hets/owl11/atermRender/*.class lib/*.jar de/unibremen/informatik/locality/*.class

get:
	ant -f OwlApi/antbuild/build.xml
	cp OwlApi/antbuild/build/owlapi-bin.jar ./lib/
	curl http://smi-protege.stanford.edu/svn/*checkout*/protege-pellet-reasoner/trunk/lib/aterm-java-1.6.jar > ./lib/aterm-java-1.6.jar
