#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

ISABELLE=${ whence isabelle_process ; }
if [[ -z ${ISABELLE} ]]; then
	warnMsg 'isabelle_process not found. Skipping Isabelle tests.'
	return 0
fi

for F in "$@" ; do
	T=${F%.thy}
	F=${T##*/}
	D=${.sh.match}
	[[ -n $D ]] && cd $D
	print " use_thy \"$F\"; quit();" | ${ISABELLE}
	(( $? )) && addErr
	[[ -n $D ]] && cd ~-
done

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
