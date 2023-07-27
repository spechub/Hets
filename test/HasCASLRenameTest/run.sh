#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

${BD}/hets -v2 -o th -n s2 Rename > log 2>&1 || addErr
OUT=${ git --no-pager diff Rename_s2.th 2>&1 ; }
[[ -n ${OUT} ]] && print -- "${OUT}" && addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
