#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

warnMsg "skipped until fixed in #2050"
return 0

${BD}/hets -v2 -o pp.dol,pp.tex,th,dfg.c -t Adl2CASL -l Adl *.adl || addErr
${BD}/hets -v2 -o pp.dol -l Adl *.dol || addErr
ls -l *.pp.dol
${BD}/hets -v2 -o pp.dol *.th || addErr
for F in ~(N)*.dfg.c ; do
	SPASS "$F" || addErr
done

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
