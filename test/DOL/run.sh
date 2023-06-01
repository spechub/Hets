#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

${BD}/hets -v2 -p parserTest.dol || addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
