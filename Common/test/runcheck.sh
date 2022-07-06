#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

PA=$1
SET=$2
ANNOS=${BD}/Common/test/Empty.annos

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

for F in ~(N)*.annos Annotations.casl ; do
	print "Processing $F ..."
	runchecker "Annotations" $F ${F}.output || addErr
	runchecker "Annos" $F ${F}.perLine.output || addErr
	runchecker "GlobalAnnos" $F ${F}.global.output || addErr
done

runmycheck MixIds casl || addErr
runwrongcheck MixIds casl || addErr
runchecker SortIds MixIds.casl MixIds.casl.asSortIds.output || addErr
runchecker VarIds MixIds.casl MixIds.casl.asVarIds.output || addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
