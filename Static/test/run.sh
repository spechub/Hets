#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${SD} || return 99

function propagateDiff {
	diff -u $1 $3 > patch
	patch $2 patch
}

function createXUpdate {
	typeset F=${1%.dol} T=${2%.dol} B

	${BD}/hets -v2 --relative-positions -o xml $F || addErr
	mv $F.xml $F.xh
	${BD}/hets -v2 --relative-positions -A -o xml $F || addErr
	mv $F.xml $F.xhi
	cp $1 $1.bak
	propagateDiff $1 $1 $2
	${BD}/hets -v2 --relative-positions -o xml $F || addErr
	mv $F.xml $F.new.xh
	cp $1.bak $1

	B=${T##*/}
	# typeset D=${PWD}
	# cd ${HETS_GMOC}
	# rm -f tmp/*.xupdate
	# rm -f tmp/*.imp
	# bin/gmoc -c Configuration.xml -itype file moc \
	#	$D/$F.xh $D/$F.xhi $D/$F.new.xh
	# mv tmp/*.xupdate $D/$B.xupdate
	# mv tmp/*.imp $D/$B.imp
	# cd -

	# cp $D/$F.xh $D/$F.hetsdginternxml
	# cp $D/$F.new.xh $D/$F.new.hetsdginternxml
	# cd ${HETS_GMOC2}
	# bin/gmoc -itype file -otype diff -o $D/$B.xupdate2 sdiff \
	#	$D/$F.hetsdginternxml $D/$F.new.hetsdginternxml
	# cd -

	${BD}/Common/testxmldiff $F.xh $F.new.xh > $B.xupdate3 || addErr
}

function createUpdates {
	typeset I J K
	for I in Spec.dol ; do
		for J in Add Remove Modify ; do
			for K in Symbol Axiom Theorem ; do
				createXUpdate $I $J$K$I
			done
		done
	done
	for I in Spec2.dol Spec3.dol ; do
		for J in Add Remove ; do
			createXUpdate $I ${J}Node$I
		done
	done
}

function callHets {
	for F in *Spec.xupdate3 ; do
		${BD}/hets -v2 --relative-positions -U $F Spec.dol || addErr
		cp Spec.xml $F.xml
	done
	for F in *Spec2.xupdate3 ; do
		${BD}/hets -v2 --relative-positions -U $F Spec2.dol || addErr
		cp Spec2.xml $F.xml
	done
	for F in *Spec3.xupdate3 ; do
		${BD}/hets -A -v2 --relative-positions -U $F Spec3.dol || addErr
		cp Spec3.xml $F.xml
	done
}

## uncomment the slow createUpdates if you do not have the .xupdates files
createUpdates
callHets

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
