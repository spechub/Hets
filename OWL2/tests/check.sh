#!/bin/sh

HETS_OWL_TOOLS=~/Hets/OWL2
export HETS_OWL_TOOLS

echo "\nhi !\n"

ALL=`ls`

for DIR in 4
do
    if test -d $DIR;
        then
            cd $DIR

            echo "testing for directory:" $DIR 

            mkdir res
    
            for i in *.ofn *.rdf
            do
                echo "\ncalling java for:" $i
                java -jar ../../OWL2Parser.jar file:`pwd`/$i xml >> `pwd`/res/$i.xml
            done

            cd ../../..

            echo "\ncompiling runConv...\n"

            make OWL2/scripts/runConv

            cd OWL2/tests/$DIR/res

            echo "\nrunning runConv first time..."

            for i in *.xml
            do
                echo "\ncalling runConv for:" $i
                ../../../scripts/runConv $i >> $i.xml
            done

            echo "\nrunning runConv second time..."

            for i in *.xml.xml
            do
                echo "\ncalling runConv for:" $i
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
                echo "\ncalling java for:" $i
                java -jar ../../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.xml.omn
            done

            for i in *.rdf.xml.xml *.ofn.xml.xml
            do
                echo "\ncalling java for:" $i
                java -jar ../../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.omn.omn
            done

            cd ../../../..

            echo "\ncompiling runXML...\n"

            make OWL2/scripts/runXML

            cd OWL2/tests/$DIR/res

            echo "\ncalling runXML on .xml files..."

            for i in *.rdf.xml  *.ofn.xml
            do
                echo "\ncalling runXML for:" $i
                ../../../scripts/runXML $i >> $i.xml.mno
            done

            for i in *.rdf.xml.xml *.ofn.xml.xml
            do
                echo "\ncalling runXML for:" $i
                ../../../scripts/runXML $i >> $i.mno.mno
            done

            cd ..            
    
            rm -rf res

            cd ..

            echo "\n"
            
    fi
done

echo "\nbye bye !\n"
