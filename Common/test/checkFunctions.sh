#!/bin/ksh93

integer ERR=0

# Use 256 color pallete. Keep OWL2/scripts/runTest.hs in syn with this.
BOX_OK='\E[1;38;5;40m\u{2714}\E[0m'			# bold green check sign
BOX_FAIL='\E[1;38;5;196m\u{2718}\E[0m'		# bold red cross
COLOR_GRAY='\E[0;38;5;232;48;5;255m'		# normal black on gray
COLOR_END='\E[0m'

function addErr {
	(( ERR++ ))
	(( FAIL_EARLY )) && exit ${ERR}
}

function filesOK {
	integer E=0
	[[ ! -x $1 ]] && "Missing '$1' (not executable)." && (( E++ ))
	[[ ! -f $2 ]] && "Missing input file '$2'." && (( E++ ))
	[[ ! -f $3 ]] && "Missing annotation file '$3'." && (( E++ ))
	return E
}

function errorMsg {
	(( $1 )) && \
	print "\E[1;38;5;226;48;5;196m$2: $1 errors \E[0m"	# bold, yellow, red
}

function infoMsg {
	print "\E[1;38;5;0;48;5;80m$@\E[0m"					# bold, black, cyan
}

function warnMsg {
	print "\E[1;38;5;1;48;5;226m$@\E[0m"				# bold, red, yellow
}

#parameters: progr option annofile infile outfile set?
function runcheck {
	typeset PROG=$1  # takes an option and an annofile on the command line
	typeset OPTION=$2  ANNOFILE=$3  INFILE=$4  OUTFILE=$5  SET=$6 A
	integer N

	print "testing ${OPTION}"

	filesOK "${PROG}" "${ANNOFILE}" "${INFILE}" || return 1

	${PROG} ${OPTION} ${ANNOFILE} < ${INFILE} > temp

	N=${ fgrep -c -i error temp ; }
	if [[ ! -f ${OUTFILE} ]]; then
		print " Creating missing comparison file ${OUTFILE}"
		cat temp > "${OUTFILE}"
		return 0
	fi
	diff temp "${OUTFILE}" > /dev/null  && print " passed" && return 0

	print " diff failed with ${OUTFILE}"
	[[ ${SET} = 'set' ]] && cat temp > "${OUTFILE}"
	A=( ${ wc -l "${INFILE}" ; } )
	M=$A
	(( N && N != M )) && print " $N errors for $M input lines"
	return 2
}

function runchecker {
	runcheck "${PA}" "$1" "${ANNOS}" "$2" "$3" ${SET}
}

#parameters: option extension
function runmycheck {
	runchecker "$1" "$1.$2" "$1.$2.output" ${SET}
} 

function runwrongcheck {
	runchecker "$1" "Wrong$1.$2" "Wrong$1.$2.output" ${SET}
} 
