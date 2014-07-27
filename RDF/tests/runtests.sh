#!/bin/bash

GOOD=`ls | egrep 'test-[0-9]+.ttl'`
BAD=`ls | egrep 'bad-[0-9]+.ttl'`

HETS="../../hets"

function clean {
	grep -v '^$' ./out/${BASENAME}.ttl_test.nt 2> /dev/null
}

mkdir -p out

for f in $GOOD
do
	BASENAME=`basename $f .ttl`
	echo "logic RDF" > ./out/${BASENAME}.ttl
	echo "spec test =" >> ./out/${BASENAME}.ttl
        echo "@base <http://www.w3.org/2001/sw/DataAccess/df1/tests/$BASENAME.ttl> ." >> ./out/${BASENAME}.ttl
        cat $f >> ./out/${BASENAME}.ttl
	rm -f ./out/${BASENAME}.ttl_test.th
	$HETS ./out/${BASENAME}.ttl -o nt > ./out/${BASENAME}.hetsout
        clean > ./out/${BASENAME}.out
	sort -k1,4 ./out/${BASENAME}.out > ./out/${BASENAME}.out.sorted
        sort -k1,4 ./${BASENAME}.out > ./${BASENAME}.out.sorted
	diff -q ./out/${BASENAME}.out.sorted ./${BASENAME}.out.sorted
done

for f in $BAD
do
	BASENAME=`basename $f .ttl`
        echo "logic RDF" > ./out/${BASENAME}.ttl
        echo "spec test =" >> ./out/${BASENAME}.ttl
        echo "@base <http://www.w3.org/2001/sw/DataAccess/df1/tests/$BASENAME.ttl> ." >> ./out/${BASENAME}.ttl
        cat $f >> ./out/${BASENAME}.ttl
	$HETS ./out/${BASENAME}.ttl -o th > ./out/${BASENAME}.hetsout
	cat ./out/${BASENAME}.hetsout | grep "*** Error:" -q
	if [ $? -eq 1 ]; then
	    echo "Example $BASENAME should have failed!"
	fi
done
