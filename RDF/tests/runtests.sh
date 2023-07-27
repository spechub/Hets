#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

export HETS_OWL_TOOLS=${BD}/OWL2

for F in ~(N)*.rdf ~(N)*.nt ; do
	${BD}/hets -i rdf $F -o th,pp.dol || addErr
done

for F in ~(N)*.pp.dol ~(N)*.th ; do
	${BD}/hets -l RDF $F -o th,pp.dol || addErr
done

for F in ~(N)*pp* ~(N)*th* ; do
	${BD}/hets -l RDF $F || addErr
done

rm *th* *pp*

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
