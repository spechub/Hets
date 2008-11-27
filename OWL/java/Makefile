INCLUDES=.:./lib/owlapi-bin.jar:./lib/aterm-java-1.6.jar

TARGET=1.5

JC=javac

world: ant get install

small-world: install

compile:
	ant compile

store:
	ant jar

install:
	cp lib/aterm-java-1.6.jar ../lib/
	cp lib/owlapi-bin.jar ../lib/
	ant install

clean: 
	ant clean	

get:
	curl http://smi-protege.stanford.edu/svn/*checkout*/protege-pellet-reasoner/trunk/lib/aterm-java-1.6.jar > ./lib/aterm-java-1.6.jar

ant: 
	ant -f OwlApi/antbuild/build.xml binjar
	cp OwlApi/antbuild/build/owlapi-bin.jar ./lib/
