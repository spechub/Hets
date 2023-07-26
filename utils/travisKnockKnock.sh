#!/bin/ksh93

typeset -r VERSION='1.0' FPROG=${.sh.file} PROG=${FPROG##*/} SDIR=${FPROG%/*}
typeset -ia -r TIMELINE=( 5 5 5 10 5 5 10 5 )
typeset -r S='###############################################################'

function showUsage {
	[[ -n $1 ]] && X='-?' ||  X='--man'
	getopts -a ${PROG} "${ print ${USAGE} ; }" OPT $X
}

function makeInstall {
	for I in ${TIMELINE[@]} ; do
		print "$0: sleeping $I s"
		sleep $I
	done
}

function showVMinfo {
	print "$S"
	cat /proc/{cpuinfo,meminfo}
	print "$S"
	swapon
	print "$S"
	df -h
	print "$S"
	df -h .
	print "$S"
	df -h /tmp
	print "$S"
	mount
	print "$S"
}

function showProcInfo {
	# who the fuck cares about kernel processes when using ps
	ps -eo user,pid,ppid,pcpu,pmem,vsz,rss,s,etime,cmd | sed -re '/[0-9] \[/ d'
}

function doMain {
	(( TIMEOUT < 5 )) && print -u2 'Adjusting timeout to 5s' && TIMEOUT=5
	(( LC < 1 )) && print -u2 'Adjusting max. loops to 100' && LC=100

	typeset L X
	integer IPID I MIPID=1 P R

	(( VERBOSE )) && showVMinfo
	(( LIMIT = MB_LIMIT * 1024 * 1024 ))
	(( LIMIT < 1024 )) && print -u2 'Adjusting RAM limit to 1 MiB' && LIMIT=1024
	if [[ -z $XFILE ]]; then
		(( SIMU )) && XFILE=( ${XFILE_DEFAULT//,/ } ) || \
			XFILE=( ${XFILE_DEFAULT[1]//,/ } )
	fi
	(( SIMU )) && trap "rm -f ${XFILE[@]}" EXIT
	(( ! SIMU )) && [[ -z ${MNAME} ]] && MNAME=${MNAME_DEFAULT}
	(( IV < 0 )) && print -u2 'Intervall-Check disabled.' && IV=0
	print "Checkpoints: ${XFILE[@]}\n$S"
	(( MPID )) && MIPID=0
	[[ -n ${MNAME} ]] && MIPID=0
	while (( LC > 0 )); do
		"${CMD[@]}" |&
		IPID="$!"
		print "'${CMD[@]}' is running with PID ${IPID}"
		SECONDS=0
		(( LC-- ))
		while true; do
			read -p -t ${TIMEOUT} L
			if (( $? )) || (( IV > 0 && SECONDS > IV )); then
				SECONDS=0
				# no input from co-pro: really busy, or swapping, or almost dead
				kill -0 ${IPID} 2>/dev/null || break	# gone
				(( VERBOSE )) && showProcInfo
				unset A ; typeset -a A
				# first match wins
				(( MPID )) && A+=( ${ ps -o rss= -o pid= -p ${MPID} ; } )
				[[ -n $MNAME ]] && A+=( ${ ps -C ${MNAME} -o rss= -o pid= ; } )
				(( MIPID )) && A+=( ${ ps -o rss= -o pid= -p ${IPID} ; } )
				set -- ${A[*]}
				while [[ -n $1 ]]; do
					R=$1
					P=$2
					shift 2
					(( R && P )) || continue
					(( R *= 1024 ))
					printf "\nCurrent RSS of %d: %#d\n" $P $R
					(( R < LIMIT )) && continue
					print "Ooops, that's too much." && kill ${IPID}
					break
				done
			fi
			print "$L"
			L=
		done
		I=1
		for X in ${XFILE[@]} ; do
			[[ ! -e $X ]] && print "Waiting for $X ..." && I=0 && break
		done
		(( I )) && break
	done
	return 0
}

unset TIMEOUT SIMU VERBOSE CMD XFILE XFILE_DEFAULT MB_LIMIT LIMIT MPID IV LC \
	MNAME
integer TIMEOUT=300 SIMU=0 VERBOSE=0 MB_LIMIT=4096 LIMIT MPID=0 IV=0 LC=0
typeset -a CMD=( 'make' 'install' ) XFILE \
	XFILE_DEFAULT=( '/tmp/hets.done' 'hets.bin,hets_server.bin')
typeset MNAME_DEFAULT='ghc' MNAME=

USAGE="[-?${VERSION}"' ]
[-copyright?Copyright (c) 2018 Jens Elkner. All rights reserved.]
[-license?CDDL 1.0]
[+NAME?'"${PROG}"' - "make hets" helper for travis]
[+DESCRIPTION?The main problem with travis-CI is, that such containers are right now (2018) limited to 7.5 GB RAM, but e.g. ghc needs more to compile and assemble hets in one row (xenial: ~10.6 GiB). Also it seems, that the hosting machine is severely overbooked, and even if only half of the RAM is consumed, it seems that the VM starts swapping and feels sluggish. Finally what we see is, that the VM silently dies and the VM monitor kills it after not having seen some output for more than 10 minutes.]
[+?So what we are trying to do is to run "make install" (or any other simple command) as a co-process and monitor it incl. proxying its output. If the co-process did not emit some output within the last \atimeout\a seconds, the script checks the RAM (resident set size) used by it or optionally another process specified via a CLI option instead. If it is not over a certain limit, the script emits the current size of the monitored process (make travis happy), and continues. Otherwise the co-process gets killed and started again unless the expected files given via option \b-x ...\b exist. Because the monitored process may get over the limit even without hitting the output timoeout, one may also specify via option \b-i ...\b, that the memory check should be done periodically after a line of output has been received from the co-process.]
[h:help?Print this help and exit.]
[F:functions?Print a list of all functions available.]
[T:trace]:[functionList?A comma separated list of functions of this script to trace (convinience for troubleshooting).]
[+?]
[c:cmd]:[command?Runs the given simple \acommand\a as co-process instead of '"${CMD[@]}"'. In this case option \b-k ...\b is probably valueable as well.]
[i:intervall]:[time?Check for RAM usage in the interval of \atime\a seconds as well. However, this happens only, when a new line of the co-process output has been read. This might be helpful to limit RAM usage even if no output timeout wrt. the co-process happens.]
[l:loops]:[num?Do not restart the co-process more than \anum\a times. Default: '"${LC}"']
[n:name]:[cmd?Monitor the process with the given \acmd\a name wrt. RAM usage instead of the co-process (ps -C \acmd\a ...). Default: unset if option \b-S\b is given as well, '"\b${MNAME_DEFAULT}\b"' otherwise.]
[p:pid]:[pid?Monitor the process with the given \apid\a wrt. RAM usage instead of the co-process.]
[S:simulate?Try to simulate the behavior by not running '"${CMD[@]}"' as co-process, but a simple loop, which just outputs something and than sleeps for a while and continues until the end of the timeline ('"${TIMELINE[@]}"' in seconds).]
[s:size]:[mb?Set the RAM usage (resident set size) limit in \amb\a for the monitored process. Default: '"${LIMIT}"']
[t:timeout]:[seconds?Number of seconds to wait for new output. Default: '"${TIMEOUT}"']
[v:verbose?Show some more details about what is going on.]
[x:xfile]:[list?Determine, whether to restart the co-process. If any of the pathes in the given comma separated \alist\a do not exist, it gets started again. If \b-S\b was given as well, those pathes get removed on exit. Default: '"'${XFILE_DEFAULT[1]}'  or '${XFILE_DEFAULT}' if \b-S\b is given."']
[
[+EXAMPLES]{
	[+'"${PROG}"' -S -t 6 -s 2]
	[+'"${PROG}"' -S -t 6 -s 3]
	[+cd Hets ; utils/'"${PROG}"' -t 10]
}
[+NOTES?Files names and other options are expected to contain ASCII printable characters, only (i.e. [-_0-9a-zA-Z/]]). Otherwise expect to get into trouble (you deserve it in this case).]
}
'
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
		c) CMD=( ${OPTARG} ) ;;
		i) IV=${OPTARG} ;;
		l) LC=${OPTARG} ;;
		n) MNAME=${OPTARG} ;;
		p) MPID=${OPTARG} ;;
		S) CMD=( 'makeInstall' ) ; MNAME= ; SIMU=1 ;;
		s) MB_LIMIT=${OPTARG} ;;
		t) TIMEOUT=${OPTARG} ;;
		v) VERBOSE=1 ;;
		x) XFILE+=( ${OPTARG//,/ } ) ;;
		*) showUsage 1 ; exit 1 ;;
	esac
done

X=$((OPTIND-1))
shift $X && OPTIND=1
unset X

doMain "$@"
