INCLUDES=.:owlapi-bin.jar

TARGET=1.5

JC=javac

world: get unpack compile store install

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
	jar cmf ./MANIFEST.MF OWL2ATerm.jar org/hets/owl11/atermRender/*.class aterm/* edu/* jjtraveler/* org/coode/* com/* de/* org/semanticweb/* shared/* uk/*
	jar cmf ./MANIFEST-LOCALITY.MF OWLLocality.jar aterm/* edu/* jjtraveler/* org/coode/* com/* de/* org/semanticweb/* shared/* uk/*

install:
	cp OWL2ATerm.jar ..
	cp OWLLocality.jar ..

clean: 
	rm -r OWL2ATerm.jar OWLLocality.jar ./org/hets/owl11/atermRender/*.class aterm edu jjtraveler owlapi.zip shared uk org/coode org/semanticweb aterm-java-1.6.jar owlapi-src.jar owlapi-bin.jar de/uulm com license.txt build.xml javadoc releasenotes.txt lib

get:
	ant -f OwlApi/antbuild/build.xml
	cp OwlApi/antbuild/build/owlapi-bin.jar .
	curl http://smi-protege.stanford.edu/svn/*checkout*/protege-pellet-reasoner/trunk/lib/aterm-java-1.6.jar > aterm-java-1.6.jar

unpack:
	unzip -oq aterm-java-1.6.jar
	unzip -oq owlapi-bin.jar
	rm -r META-INF
