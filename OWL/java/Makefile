INCLUDES=.

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

store:
	jar cmf ./MANIFEST.MF OWL2ATerm.jar org/hets/owl11/atermRender/*.class aterm/* edu/* jjtraveler/* org/antlr/* org/apache/* org/coode/* org/semanticweb/* shared/* uk/*

source-pkg:
	jar cmf ./MANIFEST.MF OWL2ATerm.src.jar org/hets/owl11/atermRender/*.java

all-pkg:
	jar cmf ./MANIFEST.MF OWL2ATerm.full.jar org/hets/owl11/atermRender/* aterm/* edu/* jjtraveler/* org/antlr/* org/apache/* org/coode/* org/semanticweb/* shared/* uk/*

install:
	cp OWL2ATerm.jar ..

clean: 
	rm -r OWL2ATerm.jar ./org/hets/owl11/atermRender/*.class aterm edu jjtraveler owlapi-2.1.1 owlapi.zip shared uk org/antlr org/apache org/coode org/semanticweb aterm-java-1.6.jar

get:
	curl http://mesh.dl.sourceforge.net/sourceforge/owlapi/owlapi-2.1.1.zip  > owlapi.zip
	curl http://smi-protege.stanford.edu/svn/*checkout*/protege-pellet-reasoner/trunk/lib/aterm-java-1.6.jar > aterm-java-1.6.jar
	unzip -oq owlapi.zip

unpack:
	unzip -oq aterm-java-1.6.jar
	unzip -oq owlapi-2.1.1/lib/antlr-runtime-3.0.jar
	unzip -oq owlapi-2.1.1/lib/commons-lang-2.2.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-apibinding.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-api.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-change.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-debugging.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-dig1_1.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-functionalparser.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-functionalrenderer.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-impl.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-krssparser.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-mansyntaxparser.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-mansyntaxrenderer.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-metrics.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-oboparser.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-owlxmlparser.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-owlxmlrenderer.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-rdfapi.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-rdfxmlparser.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-rdfxmlrenderer.jar
	unzip -oq owlapi-2.1.1/lib/owlapi-util.jar
	rm -r META-INF
