#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

if [[ -z ${MAKE} ]]; then
	[[ ${ uname -s ; } == 'SunOS' ]] && MAKE=gmake || MAKE=make
fi

[[ -z ${HETS_MAGIC} ]] && export HETS_MAGIC=${PWD%/*}/magic/hets.magic

for F in ~(N)* ; do
	[[ -d $F ]] || continue
	infoMsg "  Processing $F/ ...  "
	cd "$F" || { addErr ; continue ; }

	if [[ -f Makefile ]]; then
		${MAKE} || addErr
	elif [[ -x ./run.sh ]]; then
		./run.sh || addErr
	else
		print "Nothing to be done in $F/"
	fi
	cd ..
done

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
