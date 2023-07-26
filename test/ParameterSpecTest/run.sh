#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

for F in ~(N)*.dol ; do
	${BD}/hets -v2 -A --relative-positions -o th,pp.xml,xml "$F" || addErr
done

OUT=${ git --no-pager diff ParameterSpecTest_X_inv.th \
	ParamView.pp.xml ParamView.xml 2>&1 ; }
[[ -n ${OUT} ]] && print -- "${OUT}" && addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
