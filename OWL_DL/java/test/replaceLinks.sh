#!/bin/sh

echo `pwd` > /tmp/.changed-path
CHANGED_PWD=`sed "s/\//\\\\\\\\\//g" /tmp/.changed-path`

for i in *.owl *.xml
do
    sed -e "s/http:.*\\/\(.*\.\(owl\\|xml\)\)/file:\\/\\/`echo $CHANGED_PWD`\\/\1-local/" $i > $i-local
done