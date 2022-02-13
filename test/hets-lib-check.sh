#!/bin/ksh93

FLIST="${.sh.file%/*}/hets-lib-testfiles"
[[ -z $HETS_LIB_REPO ]] && HETS_LIB_REPO=https://github.com/spechub/Hets-lib.git
[[ -z $PREFIX ]] && export PREFIX=/tmp/hets

cd ${FLIST%/*/*}

integer E=0 FAIL_EARLY=1
[[ -n $1 ]] && FAIL_EARLY=0

if [[ ! -e ${FLIST} ]]; then
	print -u2 "${FLIST} not found. Exiting."
	exit 99
fi
[[ -x ./hets ]] && HETS='./hets' || HETS=`which hets`
if [[ -z ${HETS} ]]; then
	printf "hets not found. Exiting.\n"
	exit 98
fi

if [[ -z ${HETS_LIB} ]]; then
	if [[ -d ${PREFIX}/lib/hets/hets-lib ]]; then
		HETS_LIB=${PREFIX}/lib/hets/hets-lib
	elif [[ -d /usr/lib/hets/hets-lib ]]; then
		HETS_LIB=/usr/lib/hets/hets-lib
	else
		HETS_LIB=${PREFIX}/lib/hets/hets-lib
	fi
	print -u2 'HETS_LIB env var is empty. Setting it to '"'${HETS_LIB}'."
	export HETS_LIB
fi

[[ -e ${HETS_LIB}/Basic/Graphs.casl ]] || \
	git clone --depth=1 "${HETS_LIB_REPO}" "${HETS_LIB}"

[[ -z ${HETS_OWL_TOOLS} ]] && \
	export HETS_OWL_TOOL=${PREFIX}/lib/hets/hets-owl-tools
[[ -e ${HETS_OWL_TOOL}/OWL2Parser.jar ]] || make install-owl-tools

print "Testing named files in ${FLIST} from ${HETS_LIB} ..."
while read F ; do
	${HETS} --quiet -a none ${HETS_LIB}/$F || (( E++ ))
	if (( FAIL_EARLY && E )) ; then
		print -u2 "\E[1;38;5;9;48;5;118mFailed command:\E[0m\n" \
			"HETS_LIB=${HETS_LIB} HETS_OWL_TOOL=${HETS_OWL_TOOL}" \
			"${HETS} --quiet -a none ${HETS_LIB}/$F"
		exit 1
	fi
done<${FLIST}

COL='38;5;232;48;5;118' MSG="$N tests done."
if (( E )); then
	MSG="$E of $N tests failed."
	COL='38;5;9;48;5;118'
fi
printf "\E[1;${COL}m${MSG}\E[0m"
exit $E
