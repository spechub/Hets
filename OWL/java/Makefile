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
	ant copy-libs
	ant install

clean: 
	ant clean	

get:
	ant get

ant: 
	ant owl-api
