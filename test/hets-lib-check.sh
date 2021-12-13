#!/bin/bash

FLIST="$(dirname $0)/hets-lib-testfiles"
declare -i E=0 FAIL_EARLY=1
[[ -n $1 ]] && FAIL_EARLY=0

if [[ ! -e ${FLIST} ]]; then
	printf "${FLIST} not found. Exiting.\n"
	exit 99
fi
[[ -x ./hets ]] && HETS='./hets' || HETS=`which hets`
if [[ -z ${HETS} ]]; then
	printf "hets not found. Exiting.\n"
	exit 98
fi

printf "Testing named files in ${FLIST} from ${HETS_LIB:-/} ...\n"
while read F ; do
	./hets --quiet -a none ${HETS_LIB}/$F || (( E++ ))
	(( FAIL_EARLY && E )) && exit 1
done<${FLIST}

COL='38;5;232;48;5;118' MSG="$N tests done."
if (( E )); then
	MSG="$E of $N tests failed."
	COL='38;5;9;48;5;118'
fi
printf "\E[1;${COL}m${MSG}\E[0m"
exit $E
