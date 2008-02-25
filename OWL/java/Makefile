INCLUDES=.

TARGET=1.5

JC=javac

world: get unpack compile store install

small-word: compile store install

compile:

	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermFormat.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/ATermFunc.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermObjectRenderer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermRenderer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWLATermStorer.java
	$(JC) -target $(TARGET) -cp $(INCLUDES) ./org/hets/owl11/atermRender/OWL2ATerm.java

store:
	jar cvf OWL2ATerm.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*.class aterm/* edu/* jjtraveler/* org/antlr/* org/apache/* org/coode/* org/semanticweb/* shared/* uk/*

source-pkg:
	jar cvf OWL2ATerm.src.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*.java

all-pkg:
	jar cvf OWL2ATerm.full.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*

install:
	cp OWL2ATerm.jar ..

clean: 
	rm -r OWL2ATerm.jar ./org/hets/owl11/atermRender/*.class aterm edu jjtraveler owlapi-2.1.1 owlapi.zip shared uk org/antlr org/apache org/coode org/semanticweb

get:
	curl http://mesh.dl.sourceforge.net/sourceforge/owlapi/owlapi-2.1.1.zip  > owlapi.zip
	unzip -o owlapi.zip

unpack:
	mkdir META-BACK
	mv META-INF/MANIFEST.MF META-BACK/MANIFEST.MF
	unzip -o contrib/aterm-java-1.6.jar
	unzip -o owlapi-2.1.1/lib/antlr-runtime-3.0.jar
	unzip -o owlapi-2.1.1/lib/commons-lang-2.2.jar
	unzip -o owlapi-2.1.1/lib/owlapi-apibinding.jar
	unzip -o owlapi-2.1.1/lib/owlapi-api.jar
	unzip -o owlapi-2.1.1/lib/owlapi-change.jar
	unzip -o owlapi-2.1.1/lib/owlapi-debugging.jar
	unzip -o owlapi-2.1.1/lib/owlapi-dig1_1.jar
	unzip -o owlapi-2.1.1/lib/owlapi-functionalparser.jar
	unzip -o owlapi-2.1.1/lib/owlapi-functionalrenderer.jar
	unzip -o owlapi-2.1.1/lib/owlapi-impl.jar
	unzip -o owlapi-2.1.1/lib/owlapi-krssparser.jar
	unzip -o owlapi-2.1.1/lib/owlapi-mansyntaxparser.jar
	unzip -o owlapi-2.1.1/lib/owlapi-mansyntaxrenderer.jar
	unzip -o owlapi-2.1.1/lib/owlapi-metrics.jar
	unzip -o owlapi-2.1.1/lib/owlapi-oboparser.jar
	unzip -o owlapi-2.1.1/lib/owlapi-owlxmlparser.jar
	unzip -o owlapi-2.1.1/lib/owlapi-owlxmlrenderer.jar
	unzip -o owlapi-2.1.1/lib/owlapi-rdfapi.jar
	unzip -o owlapi-2.1.1/lib/owlapi-rdfxmlparser.jar
	unzip -o owlapi-2.1.1/lib/owlapi-rdfxmlrenderer.jar
	unzip -o owlapi-2.1.1/lib/owlapi-util.jar
	mv META-BACK/MANIFEST.MF META-INF/MANIFEST.MF
	rm -r META-BACK
	rm META-INF/LICENSE.txt
	rm META-INF/NOTICE.txt
	rm -r META-INF/maven
