#!/bin/sh

HETS_OWL_TOOLS=~/Hets/OWL2
export HETS_OWL_TOOLS

echo "\nSTART"

DIRS=1

for DIR in $DIRS
do
    cd $DIR

    echo "\nTESTING FOR DIRECTORY:" $DIR 

    mkdir res
    
    for i in *.ofn *.rdf
    do
        echo "\njava for:" $i
        java -jar ../../OWL2Parser.jar file:`pwd`/$i xml >> `pwd`/res/$i.xml
    done

    cd ../../..

    echo "\ncompiling runConv...\n"

    make OWL2/scripts/runConv

    cd OWL2/tests/$DIR/res

    echo "\nrunning runConv first time..."

    for i in *.xml
    do
        echo "\nrunConv for:" $i
        ../../../scripts/runConv $i >> $i.xml
    done

    echo "\nrunning runConv second time..."

    for i in *.xml.xml
    do
        echo "\nrunConv for:" $i
        ../../../scripts/runConv $i >> $i.xml
    done

    cd ../../../..

    echo "\ncalling hets for all xml files...\n"

    for i in OWL2/tests/$DIR/res/*.xml
    do
        ./hets -i ow2 $i
        echo "\n"
    done

    echo "creating omn files with java..."

    cd OWL2/tests/$DIR/res

    for i in *.rdf.xml *.ofn.xml
    do
        echo "\njava for:" $i
        java -jar ../../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.xml.omn
    done

    for i in *.rdf.xml.xml *.ofn.xml.xml
    do
        echo "\njava for:" $i
        java -jar ../../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.omn.omn
    done
done

echo "\nEND\n"
