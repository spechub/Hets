#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

set -o xtrace

${BD}/hets -v2 -L ${HETS_LIB}:.. Heat.hpf || addErr

set +o xtrace

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
