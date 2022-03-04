#!/bin/ksh93

#first parameter is executable
#second parameter resets ouput files

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

PA=$1
SET=$2
ANNOS=${BD}/Common/test/Standard.annos

#extra test
runchecker Terms ${BD}/Common/test/MixIds.casl \
	MixIds.casl.asTerms.output || addErr
runchecker Terms ${BD}/Common/test/WrongMixIds.casl \
	WrongMixIds.casl.asTerms.output || addErr
runchecker MixfixTerms Terms.casl \
	Terms.casl.asMixfixTerms.output || addErr
runchecker MixfixFormula Formula.casl \
	Formula.casl.asMixfixFormula.output || addErr

# don't take files starting with "Wrong"
for F in [A-V]*.casl ; do
	T=${F%.casl}
	T=${T##*/}
	runmycheck "$T" casl || addErr
	runwrongcheck "$T" casl || addErr
done

for F in [X-Z]*.casl ; do
    runchecker sentences "$F" "${F}.output" || addErr
done

runchecker analysis BasicSpec.casl BasicSpec.analysis.output || addErr
runchecker signature BasicSpec.casl BasicSpec.signature.output || addErr
runchecker sentences BasicSpec.casl BasicSpec.sentences.output || addErr

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
