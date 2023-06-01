#!/bin/ksh93

# SPASS must be in $PATH

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd $1
export LOG=${ printf "${PWD}/spass_%(%F-%T)T.log" now ; }	#" make vim happy

# cleaning up of old files (snd part is dangerous)
rm -f Basic/*.env Basic/*.dfg
print "log goes to ${LOG}"

function runJob {
	# generating dfg files
	${BD}/hets -o dfg Basic/*.casl || addErr

	# checking dfg files with SPASS
	for F in Basic/*.dfg ; do
		print $F
		SPASS -Auto=0 $F || addErr
	done
}
time runJob 2>&1 | tee ${LOG}
(( ! ERR ))
