#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

${BD}/hets -v2 -A -o thy *.dol || addErr
${BD}/utils/nightly/runisabelle.sh *.thy || addErr

${BD}/hets -l HasCASL -v2 -A -o thy *.dol || addErr
${BD}/utils/nightly/runisabelle.sh *.thy || addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
