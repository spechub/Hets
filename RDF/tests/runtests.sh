#!/bin/bash

GOOD=`ls | egrep 'test-[0-9]+.ttl'`
BAD=`ls | egrep 'bad-[0-9]+.ttl'`
BASE="@base <http://www.w3.org/2001/sw/DataAccess/df1/tests/> ."

HETS="../../hets"

function clean {
	cat /tmp/test.ttl_test.th | grep -v "logic RDF" | \
         grep -v "spec <tmp/testttl?test> =" | \
         grep -v "^\#" | grep -v "^$"
}

for f in $GOOD
do
	echo "logic RDF" > /tmp/test.ttl
	echo "spec test =" >> /tmp/test.ttl
        echo $BASE >> /tmp/test.ttl
        cat $f >> /tmp/test.ttl
	$HETS /tmp/test.ttl -o th > /dev/null
        clean > /tmp/test.out
	OUTFILE="`dirname $f`/`basename $f .ttl`.out"
	diff -q /tmp/test.out $OUTFILE
done
