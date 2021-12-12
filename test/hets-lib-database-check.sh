#!/bin/ksh93

# -------------- private ----------------

typeset -r VERSION='1.0' FPROG=${.sh.file} PROG=${FPROG##*/} SDIR=${FPROG%/*}
TEST_FILES=$(<${SDIR}/hets-lib-database-testfiles)

# Base directory for the PostgreSQL DB used for testing. Should be writeable
# by the user, running this script. This script should not be run as 'root'.
# Requires ~ 250 MB free space (2018-06).
[[ -d /var/ramfs ]] && DATADIR=/var/ramfs || DATADIR=/tmp
DATADIR+='/hets-testdata'
[[ -z ${TEST_DATADIR} ]] && TEST_DATADIR="${DATADIR}"

DB_FILE="${TEST_DATADIR}/hets.sqlite"
DB_GAMML="${TEST_DATADIR}/pg.yml"

export PG_DBA='postgres' PGBIN=${ pg_config --bindir 2>/dev/null ; } \
	PGDATA=${TEST_DATADIR}/db/main PGHOST=${TEST_DATADIR}/var PGPORT=15000

[[ ${ uname -s ; } == 'SunOS' ]] && SED='gsed' || SED='sed'

function checkPgBin {
	[[ -n ${PGBIN} && -x ${PGBIN}/pg_isready ]] && return 0
	dpkg -S pg_ctl | while read PKG FILE TAIL ; do
		if [[ ${FILE: -11:11} == '/bin/pg_ctl' && \
			${FILE} != '/usr/bin/pg_ctl' ]]
		then
			PGBIN="${FILE%/*}"
			return 0
		fi
	done
	return 1
}

function initPgDB {
	checkPgBin || return 1
	mkdir -p "${PGHOST}" "${PGDATA%/*}" || return 2
	if [[ ! -x ${PGBIN}/initdb ]]; then
		print -u2 "Uhmm '${PGBIN}/initdb' is not executable!"
		return 3
	fi

	print 'Initializing PostgreSQL server ...'
	${PGBIN}/pg_ctl init -s -w -m fast \
		-o "-E UTF8 --locale=en_US.UTF-8 --username=${PG_DBA}"
	typeset PROP='unix_socket_directories'
	${SED} -i -e "/^#${PROP}/ s,^.*,${PROP} = '${PGHOST}'," \
		-e "/^#port/ s,^.*,port = ${PGPORT}," \
		${PGDATA}/postgresql.conf

	print '\nStarting PostgreSQL server ...'
	${PGBIN}/pg_ctl -s -w start || return $?
	# stupid yaml brain damage causes hets not to behave like normal pgsql
	# clients - welcome to the dark ages of CS ...
	${SED} -r -e "/^  (# *)?port/ s,^.*,  port: ${PGPORT}," \
		Persistence/database_postgresql.yml >${DB_GAMML}
}

function shutdownPgDb {
	X=${ pgrep -u ${LOGNAME} postgres ; }
	[[ -z $X ]] && return
	checkPgBin && ${PGBIN}/pg_ctl -w -m fast stop
	# just in case
	X=${ pgrep -u ${LOGNAME} postgres ; }
	[[ -n $X ]] && pkill -u ${LOGNAME} postgres
}

function cleanup {
	print 'Cleanup ...'
	[[ ${DB} == 'PostgreSQL' ]] && shutdownPgDb
	(( KEEP )) && print "Keeping '${TEST_DATADIR}/' as is." && return 0
	rm -rf "${TEST_DATADIR:-/empty}/"*
	return 0
}

function showUsage {
	[[ -n $1 ]] && X='-?' ||  X='--man'
	getopts -a ${PROG} "${ print ${USAGE} ; }" OPT $X
}

function resetDB {
	du -sh ${TEST_DATADIR}
	if [[ $1 == 'PostgreSQL' ]]; then
		psql -U ${PG_DBA} -c 'drop database hets_test;' >/dev/null
		psql -U ${PG_DBA} -c 'create database hets_test;' >/dev/null
	elif [[ $1 == 'MySQL' ]]; then
		mysql -u root -e 'drop database if exists hets_test;'
		mysql -u root -e 'create database hets_test;'
	elif [[ $1 == 'SQLite' ]]; then
		rm -f "${DB_FILE}"
	else
		print -u2 "Unsupported database '${DB}'."
		return 1
	fi
}

function populateDB {
	typeset -n CMD=$1
	"${CMD[@]}" --logic-graph
}

function setupBaseCmd {
	typeset -n CMD=$1
	if [[ $2 == 'PostgreSQL' || $2 == 'MySQL' ]]; then
		CMD=( 'hets-server'
			"--database-config=${DB_GAMML}"
			'--database-subconfig=test'
		)
	elif [[ $2 == 'SQLite' ]]; then
		CMD=( 'hets'
			"--database-file=${DB_FILE}"
		)
	else
		print -u2 "Unsupported database '$2'."
		return 1
	fi
	CMD+=( '--quiet' '--output-types=db' )
	return 0
}

function doMain {
	typeset -a CMD
	integer E=0 N=0
	[[ -z $1 ]] && showUsage 1 && return 0

	setupBaseCmd CMD $1 && DB=$1 || return 1

	[[ ${DB} == 'PostgreSQL' ]] && shutdownPgDb	# just in case

	if [[ -e ${TEST_DATADIR} ]]; then
		rm -rf "${TEST_DATADIR}/"* || return 2
	else
		mkdir -p ${TEST_DATADIR} || return 3
	fi
	if [[ ${DB} == 'PostgreSQL' ]]; then
		initPgDB || return 2
	fi

	resetDB ${DB} >/dev/null 2>&1		# irritating
	(( TODO & 2 )) && populateDB CMD
	(( TODO )) && return 0

	print "${CMD[@]}"
	for F in ${TEST_FILES}; do
		(( N++ ))
		if populateDB CMD ; then
			print "${CMD[@]}" ${HETS_LIB:-.}/$F
			"${CMD[@]}" ${HETS_LIB:-.}/$F || (( E++ ))
		else
			(( E++ ))
		fi
		resetDB ${DB}
		(( FAIL_EARLY && E )) && return 1
	done
	typeset COL='38;5;232;48;5;118' MSG="$N ${DB} tests done."
	if (( E )); then
		MSG="$E of $N ${DB} tests failed."
		COL='38;5;9;48;5;118'
	fi
	print -u2 "\E[1;${COL}m${MSG}\E[0m"
	return $E
}

USAGE="[-?${VERSION}"' ]
[+NAME?'"${PROG}"' - helper script to test hets DB functionality]
[+DESCRIPTION?A little script to test DB capabilities of the hets client or hets-server.]
[h:help?Print this help and exit.]
[F:functions?Print a list of all functions available.]
[T:trace]:[functionList?A comma separated list of functions of this script to trace (convinience for troubleshooting).]
[+?]
[r:reset?Just drop and re-create the related DB and exit.]
[p:populate?Just drop, re-create and populate the related DB and exit.]
[k:keep?Do not cleanup the \bTEST_DATADIR\b on exit.]
[a:all?Try all files, ignore errors. Per default the first error would stop the test.]
[+ENVIRONMENT]{
	[+TEST_DATADIR?The directory to use for creating test databases and files. All files and directories inside this one get removed on demand without notice! Default: '"${DATADIR}"']
	[+HETS_LIB?The directory containing the test files. Default: .]
}
\n\n{\bPostgreSQL\b|\bMySQL\b|\bSQLite\b}
'
unset TODO KEEP FAIL_EARLY
integer TODO=0 KEEP=0 FAIL_EARLY=1

X="${ print ${USAGE} ; }"
while getopts "${X}" OPT ; do
	case ${OPT} in
		h) showUsage ; exit 0 ;;
		T)	if [[ ${OPTARG} == 'ALL' ]]; then
				typeset -ft ${ typeset +f ; }
			else
				typeset -ft ${OPTARG//,/ }
			fi
			;;
		F) typeset +f && exit 0 ;;
		a) FAIL_EARLY=0 ;;
		k) KEEP=1 ;;
		r) TODO|=1 ;;
		p) TODO|=3 ;;
		*) showUsage 1 ; exit 1 ;;
	esac
done

X=$((OPTIND-1))
shift $X && OPTIND=1
unset X
trap cleanup EXIT

doMain "$@"
