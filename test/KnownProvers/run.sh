#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${BD} || return 99

# Test if the KnownProversMap works
Comorphisms/test/showKP || { print '  failed' && addErr && return 1; }
print '  passed'

# Test CMDL_tests
if [[ -z ${MAKE} ]]; then
	[[ ${ uname -s ; } == 'SunOS' ]] && MAKE=gmake || MAKE=make
fi

for F in SoftFOL/tests/CMDL_tests Comorphisms/test/sublogicGraph ; do
	${MAKE} $F
	$F || addErr
done

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
