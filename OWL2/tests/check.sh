#!/bin/ksh93

# - Parser Printer (own testscripts)
#   - MS
#   - AS
#   - XML
# - Calling hets on (static analysis)
#   - DOL
#   - MS
#   - AS
#   - XML

# 1. run tests for *.xml
# 2. run tests for *.omn

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

cd ${BD}

export HETS_OWL_TOOLS=${BD}/OWL2
if [[ -z ${MAKE} ]]; then
	[[ ${ uname -s ; } == 'SunOS' ]] && MAKE=gmake || MAKE=make
fi

[[ -f OWL2/OWL2Parser.jar ]] || make jars

print 'Compiling runTest...'
F=OWL2/scripts/runTest
${MAKE} $F || return 1

TESTSCRIPT=${BD}/$F

cd ${SD} || return 99

for D in . * ; do
	[[ -d $D ]] || continue
	[[ $D != '.' ]] && cd "$D"

	infoMsg "Running Functional Syntax Files in $D/ ..."
	for F in ~(N)*.ofn ; do
		[[ -f $F ]] || continue
		print "  Testing $D/$F ... "
		${TESTSCRIPT} "$F" || addErr
	done

	infoMsg "Running Manchester Syntax Files in $D/ ..."
	for F in ~(N)*.omn ; do
		[[ -f $F ]] || continue
		print "  Testing $D/$F ... "
		${TESTSCRIPT} "$F" || addErr
	done

	for F in ~(N)*.mno ; do
		[[ -f $F ]] || continue
		print "  Testing $D/$F ... "
		${TESTSCRIPT} "$F" || addErr
	done

	infoMsg "Running XML Syntax Files in $D/ ..."
	for F in ~(N)*.xml ; do
		[[ -f $F ]] || continue
		print "  Testing $D/$F ... "
		${TESTSCRIPT} "$F" || addErr
	done

	infoMsg "Running hets on all files in $D/ ..."
	for F in ~(N)*.ofn ~(N)*.omn ~(N)*.xml ~(N)*.dol # *.rdf
	do
		[[ -f $F ]] || continue
		[[ "$D" == "11" ]] && [[ "${F##*.}" == "omn" ]] && warnMsg "Skipping $D/$F until OWLAPI supporting Manchester extensions is implemented" && continue
		print "  Testing $D/$F ... "
		OUTPUT=${ ${BD}/hets "$F" 2>&1 ; }
		if (( $? )); then
			printf "${BOX_FAIL} failed:\n"
			(( ${#OUTPUT} < 1024 )) && print -- "${OUTPUT}" || \
				print -- "${COLOR_GRAY}${OUTPUT}${COLOR_END}"
			addErr
		else
			printf "${BOX_OK} success\n"
		fi
	done

	[[ "$D" == '.'  ]] || cd ~-
done

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
