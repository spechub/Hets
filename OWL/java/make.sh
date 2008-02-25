#!/bin/bash

INCLUDE="../lib/aterm-java-1.6.jar/:../lib/owlapi-api.jar/:../lib/owlapi-util.jar:../owlapi-impl.jar/:../lib/owlapi-apibinding.jar/:."

rm ./org/hets/owl11/atermRender/*.class

javac -target 1.5 -cp $INCLUDE  ./org/hets/owl11/atermRender/OWLATermFormat.java
javac -target 1.5 -cp $INCLUDE  ./org/hets/owl11/atermRender/ATermFunc.java
javac -target 1.5 -cp $INCLUDE  ./org/hets/owl11/atermRender/OWLATermObjectRenderer.java
javac -target 1.5 -cp $INCLUDE  ./org/hets/owl11/atermRender/OWLATermRenderer.java
javac -target 1.5 -cp $INCLUDE  ./org/hets/owl11/atermRender/OWLATermStorer.java
javac -target 1.5 -cp $INCLUDE  ./org/hets/owl11/atermRender/OWL2ATerm.java

jar cvf OWL2ATerm.jar META-INF/MANIFEST.MF org/hets/owl11/atermRender/*.class

mv OWL2ATerm.jar ..
