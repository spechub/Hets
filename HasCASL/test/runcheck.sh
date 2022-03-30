#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

PA=$1
SET=$2
ANNOS=${BD}/Common/test/Standard.annos

. ${BD}/Common/test/checkFunctions.sh

warnMsg "skipped until fixed in #2050"
return 0

D=${BD}/Common/test/

runchecker MixIds ${D}MixIds.casl MixIds.casl.output || addErr
runchecker MixIds ${D}WrongMixIds.casl WrongMixIds.casl.output || addErr
runchecker BasicSpec ${D}sicSpec.casl BasicSpec.casl.output || addErr
runchecker MixfixTerms ${D}xfixTerms.casl MixfixTerms.casl.output || addErr
runchecker MixfixTerms ${D}xfixFormula.casl MixfixFormula.casl.output || addErr

for T in Kinds Types Terms Items MixfixTerms ; do
    runmycheck $T hascasl || addErr
    runwrongcheck $T hascasl || addErr
done

runchecker BasicSpec BasicSpec.hascasl BasicSpec.hascasl.parser.output || addErr
runwrongcheck BasicSpec hascasl || addErr

for F in [A-HLN-SX-Z]*.hascasl ; do
	infoMsg "  Processing $F ...  "
	runchecker "analysis" $F ${F}.output || addErr
done

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
