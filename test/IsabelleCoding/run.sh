#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

${BD}/hets -v2 -o thy *.dol || addErr
${BD}/utils/nightly/runisabelle.sh *.thy || addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
