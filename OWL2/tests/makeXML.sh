#!/bin/bash

HETS_OWL_TOOLS=`pwd`/..
export HETS_OWL_TOOLS

cd ../..

[[ `uname -s` == 'SunOS' ]] && MAKE=gmake || MAKE=make
${MAKE}

cd OWL2/tests

echo "\ncreating directory XML...\n"

mkdir XML

dir=OWL2/tests/XML

echo "creating .rdf.xml files with java...\n"

for i in test*.rdf food.rdf pizza.owl *.ofn
do
    java -jar ../OWL2Parser.jar file:`pwd`/$i xml >> `pwd`/XML/$i.xml
    echo $i "ok\n"
done

cd ../..

echo "compiling runConv...\n"

${MAKE} OWL2/scripts/runConv

echo "\nrunning runConv first time...\n"

for i in OWL2/tests/XML/*.xml
do
    OWL2/scripts/runConv $i >> $i.xml
    echo $i "ok\n"
done

echo "running runConv second time...\n"

for i in $dir/*.xml.xml
do
    OWL2/scripts/runConv $i >> $i.xml
    echo $i "ok\n"
done

cd $dir

a()
{
for i in *.rdf.xml.xml *.owl.xml.xml *ofn.xml.xml 
do 
    echo $i "\n" 
    diff $i $i.xml 
done 
}
cd ../../..

a()
{
echo "calling hets for all xml files...\n"

for i in $dir/*.xml.xml
do
    ./hets -i ow2 $i
    echo "\n"
done
}
cd OWL2/tests/XML

echo "\ncreating omn files from .rdf.xml with java...\n"

for i in *.rdf.xml *.owl.xml *.ofn.xml
do
   java -jar ../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.xml.omn
   echo $i "ok\n"
done



echo "creating omn files from .rdf.xml.xml with java...\n"

for i in *.rdf.xml.xml *.owl.xml.xml *.ofn.xml.xml
do
   java -jar ../../OWL2Parser.jar file:`pwd`/$i >> `pwd`/$i.omn.omn
   echo $i "ok\n"
done

#a()
#{
for i in *.rdf.xml.xml.omn *.owl.xml.xml.omn *.ofn.xml.xml.omn 
do 
    echo $i "\n" 
    diff $i $i.omn 
done 
#}

cd ../../..

echo "compiling runXML...\n"

${MAKE} OWL2/scripts/runXML

cd OWL2/tests/XML

echo "\nrunning runXML on .rdf.xml files...\n"

for i in *.rdf.xml *.owl.xml *.ofn.xml
do
    ../../scripts/runXML $i >> $i.xml.mno
    echo $i "ok\n"
done

echo "running runXML on .rdf.xml.xml files...\n"

for i in *.rdf.xml.xml *.owl.xml.xml *.ofn.xml.xml
do
    ../../scripts/runXML $i >> $i.mno.mno
    echo $i "ok\n"
done

a()
{
for i in *.rdf.xml.xml.mno *.owl.xml.xml.mno *.ofn.xml.xml.mno 
do 
    echo $i "\n" 
    diff $i $i.mno 
done 
}
echo "removing directory XML...\n"

#rm -rf ../XML
