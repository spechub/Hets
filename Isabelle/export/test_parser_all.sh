#!/bin/bash

function path() {
        if [ "${1%/*}" = "${1##*/}" ]; then
                echo $(pwd -P)/$1
        else
                local P=`pwd`;
                cd ${1%/*} &> /dev/null && echo $(pwd -P)/${1##*/};
                local R=$?;
                cd $P &> /dev/null;
                return $R;
        fi
}

exec_test_script() {
	echo "Testing $1"
	RESULT=`$TEST_SCRIPT $1`
	if [ ! `echo "$RESULT" | grep -q "val err = \"\": string"` ]; then
		echo "$RESULT" | grep -A 2 "val err ="
		return 1
	fi
	return 0
}

SCRIPT=$(path $0)
SCRIPTPATH=`dirname "$SCRIPT"`

TEST_SCRIPT="$SCRIPTPATH/test_parser.sh"

export -f exec_test_script
export TEST_SCRIPT="$TEST_SCRIPT"

find $1 -name '*.thy' | xargs -n 1 -i bash -c 'exec_test_script "$@"' _ {} \;
