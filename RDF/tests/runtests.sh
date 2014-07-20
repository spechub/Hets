#!/bin/bash

GOOD=`ls | egrep 'test-[0-9]+.ttl'`
BAD=`ls | egrep 'bad-[0-9]+.ttl'`
BASE="@base <http://www.w3.org/2001/sw/DataAccess/df1/tests/> ."

HETS="../../hets"

function clean {
	cat ./out/${BASENAME}.ttl_test.th 2> /dev/null | \
         grep -v "logic RDF" | \
         grep -v "spec <out/.*> =" | \
         grep -v "^\#" | grep -v "^$"
}

mkdir -p out

for f in $GOOD
do
	BASENAME=`basename $f .ttl`
	echo "logic RDF" > ./out/${BASENAME}.ttl
	echo "spec test =" >> ./out/${BASENAME}.ttl
        echo $BASE >> ./out/${BASENAME}.ttl
        cat $f >> ./out/${BASENAME}.ttl
	$HETS ./out/${BASENAME}.ttl -o th > ./out/${BASENAME}.hetsout
        clean > ./out/${BASENAME}.out
	diff -q ./out/${BASENAME}.out ./${BASENAME}.out
done
