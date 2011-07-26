#!/bin/sh

HETS_OWL_TOOLS=~/Hets/OWL2
export HETS_OWL_TOOLS

ECHO="echo -e"

$ECHO "\nhi !\n"

ALL=`ls`

for DIR in $ALL
do
    if test -d $DIR;
        then
            cd $DIR

            $ECHO "testing for directory:" $DIR

            mkdir res

            for i in *.ofn *.rdf
            do
                $ECHO "\ncalling java for:" $i
                java -jar ../../OWL2Parser.jar file:`pwd`/$i xml >> `pwd`/res/$i.xml
            done

            cd ../../..

            $ECHO "\ncompiling runConv...\n"

            make OWL2/scripts/runConv

            cd OWL2/tests/$DIR/res

            $ECHO "\nrunning runConv first time..."

            for i in *.xml
            do
                $ECHO "\ncalling runConv for:" $i
                ../../../scripts/runConv $i >> $i.xml
            done

            $ECHO "\nrunning runConv second time..."

            for i in *.xml.xml
            do
                $ECHO "\ncalling runConv for:" $i
                ../../../scripts/runConv $i >> $i.xml
            done

            cd ../../../..

            $ECHO "\ncalling hets for all xml files...\n"

            for i in OWL2/tests/$DIR/res/*.xml
            do
                ./hets -i ow2 $i
                $ECHO "\n"
            done

            $ECHO "creating omn files with java..."

            cd OWL2/tests/$DIR/res

            for i in *.ofn.xml #*.rdf.xml
            do
                $ECHO "\ncalling java for:" $i
                java -jar ../../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.xml.omn
            done

            for i in *.ofn.xml.xml *.rdf.xml.xml
            do
                $ECHO "\ncalling java for:" $i
                java -jar ../../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.omn.omn
            done

            cd ../../../..

            $ECHO "\ncompiling runXML...\n"

            make OWL2/scripts/runXML

            cd OWL2/tests/$DIR/res

            $ECHO "\ncalling runXML on .xml files..."

            for i in *.ofn.xml *.rdf.xml
            do
                $ECHO "\ncalling runXML for:" $i
                ../../../scripts/runXML $i >> $i.xml.mno
            done

            for i in *.ofn.xml.xml *.rdf.xml.xml
            do
                $ECHO "\ncalling runXML for:" $i
                ../../../scripts/runXML $i >> $i.mno.mno
            done

            cd ..

            #rm -rf res

            cd ..

            $ECHO "\n"

    fi
done

$ECHO "\nbye bye !\n"
