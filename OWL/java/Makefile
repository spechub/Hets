INCLUDES="../lib/aterm-java-1.6.jar/:../lib/owlapi-api.jar/:../lib/owlapi-util.jar:../owlapi-impl.jar/:../lib/owlapi-apibinding.jar/:."

TARGET=1.5

JC=javac

world: compile store install

compile:

	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermFormat.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/ATermFunc.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermObjectRenderer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermRenderer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermStorer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWL2ATerm.java

store:
	jar cvf OWL2ATerm.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*.class

source-pkg:
	jar cvf OWL2ATerm.src.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*.java

all-pkg:
	jar cvf OWL2ATerm.full.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*

install:
	cp OWL2ATerm.jar ..

clean: 
	rm ../OWL2ATerm.jar OWL2ATerm.jar ./org/hets/owl11/atermRender/*.class
