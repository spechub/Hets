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
(( $E )) && printf "Failed with $E errors.\n" || printf "Done.\n"
exit $E
