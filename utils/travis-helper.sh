#!/bin/bash

# yaml + yaml2json produce bullshit alias unparseable files when using
# not very simple shell statements and cause travis-ci to fail. So we use this
# file to store the "not so trivial" parts of the .travis.yml and to take over
# control: The travis-ci cache mechanism is awefull dumb and inefficient.
#
# We use the limited bash because the travis-ci env definies a lot of bash
# aliases and functions, we may [ab]use to get the job done. For details see:
# ~travis/.travis/job_stages
#
# There is no intention to make this script run correctly in non-Travis-CI
# environments. If you run it outside, be prepared for getting into trouble!

# Hardware Info (2018-06)
# =======================
# travis-CI runs on 2.3, 2.5 and 2.6 GHz machines with 7.5 GB RAM/container.
# The RAM is not sufficient for compiling hets[_server] in one row (requires
# ~10..12 GB). Therefore utils/travisKnockKnock.sh gets used to monitor make
# and ghc and kill and re-start it, when the given limit has been reached.
# Killing ghc is not a problem, because ghc simply continues with the remaining
# stuff required to finally link the binary in question. For more info see
# 'utils/travisKnockKnock.sh -h'

# Caching Info (2018-06)
# ======================
# After each job execution travis-ci is looking for modifications in the dirs
# givien via .travis.yml:cache:directories: . If a single modification has been
# found, _all_ cache directories get archived and x-ferred to the google cloud
# (see ${CASHER_DIR}/bin/casher or ~travis/.travis/job_stages). Unfortunately
# the cache download and upload URLs used are signed and thus not really useful
# to inject other archives, and not really useful as well because the download
# URL expires 15 min (upload URL 3h) after the container has been booted -
# 3-5 min are usually needed for setup/install env => remaining 10..12 min are
# not sufficient to build hets|hets_server.
#
# Doing all jobs one after another does not work, because the jobs take too
# long to get finished within 50 min.  E.g. (all +-5 min because of CPUs):
#	- stack: ~25 min
#	- hets|hets_server: ~28 min
#	- each test: ~15 min
# Thus in the worst case (i.e. the 1st time a PR hits travis): 2:20h
#
# Basic Idea:
# ------------
# So the idea is to build painful stack incl. ghc only once in the 1st stage
# named 'Stack' and use it as is for all subsequent stages and builds. This
# produces ~ 2.8 GiB bloat (uncompressed) => ~ 825 MiB tgz cache archive.
#
# In the next stage we build hets (desktop version) and hets_server in parallel
# using 2 jobs. Basic idea is to not use ${TRAVIS_BUILD_DIR} which is, what
# travis-ci checks out from github and gets used per default for build. Instead
# we sync the cached dir ${HETS_BASEDIR}/{desktop|server} with it using rsync
# and its size+checksum algorithm. However, because the dumb stack stuff hard-
# codes pathes into its package DBs, meta data files, we can't use the easy way
# (2 dirs directly), but have to rename ${HETS_BASEDIR}/{desktop|server} to
# e.g. ${HETS_BASEDIR}/shared and rename it back, after the job is done.
# Unfortunately this is still not sufficient because of travis' dumb caching:
# the job which finishes 1st would package and x-fer the new cache archive
# (takes ~ 3-4 min) to google and later, when the 2nd job gets finished it does
# the same overwriting the "cache" from the 1st job. So we need to use external
# caching at least for the result of one job - best candidate is server, because
# slightly smaller and used by one test only (all other tests use the hets
# desktop version). Archiving ${HETS_BASEDIR}/{desktop|server} takes about
# 20+-5s depending on the machine and whether the final binary gets included,
# and produces a tgz of ~ 100 MB (+ 21 MB if the binary gets included). Xfer
# rate is ~ 75+-20 MiB/s so add. costs incl. extracting would be ~ 3..6s.
# Compared to the other cached stuff this is relatively cheap and thus we
# simply synchronize the desktop 'Build' job with the server 'Build' job via
# our own external cache, and pull in the "server archive cache", before the
# desktop job creates and uploads its new cache.
# A little bit better would be to always push and pull on demand the
# hets[_server] archives to the external cache, only. However, this would
# require more know-how, maintenance burden, complexity on the cacher site ...
#
# In the last stage named 'Test' we run all test jobs in parallel. We just need
# to take care of properly renaming the appropriate
# ${HETS_BASEDIR}/{desktop|server} to ${HETS_BASEDIR}/shared - same way as in
# the 'Build' stage. Because we do not need any changes we explicitly disable
# cache uploads by removing the related script: ${CASHER_DIR}/bin/casher

# Usable Travis env vars
# ======================
# TRAVIS_BUILD_ID=396668280
# TRAVIS_BUILD_NUMBER=2016
# TRAVIS_BUILD_DIR=/home/travis/build/spechub/Hets
# TRAVIS_BRANCH=master
# TRAVIS_EVENT_TYPE=pull_request
# TRAVIS_PULL_REQUEST=1853
# TRAVIS_PULL_REQUEST_BRANCH=dependency_fix
# TRAVIS_JOB_ID=396668281
# TRAVIS_JOB_NUMBER=2016.1

[[ -z "${PUSH_URL}" ]] && PUSH_URL='http://theo.cs.ovgu.de/cgi-bin/push'
[[ -z "${PULL_URL}" ]] && PULL_URL='http://theo.cs.ovgu.de/travis'
[[ -z "${HETS_BASEDIR}" ]] && HETS_BASEDIR='/var/tmp/hets'
JOB_NAME=$(</tmp/JOB_NAME)

# show some system infos to aid troubleshooting
function myShowInfo {
	local SEP='###################################'
	echo ${SEP}
	echo "Job: ${JOB_NAME} ${TRAVIS_JOB_NUMBER}"
	echo ${SEP}
	egrep '^model name' /proc/cpuinfo
	echo ${SEP}
	egrep '^(Mem|Swap)' /proc/meminfo
	echo ${SEP}
	[[ -z "$1" ]] && return 0
	echo ${SEP}
	env
	[[ "$1" == 'full' && -f /tmp/set.out ]] && echo ${SEP} && cat /tmp/set.out
	echo ${SEP}
	df -h
	echo ${SEP}
	pwd
	df -h .
	echo ${SEP}
	ls -alR /var/ramfs
	echo ${SEP}
	echo ${HETS_BASEDIR}/server
	echo ${SEP}
	ls -al ${HETS_BASEDIR}/server
	echo ${SEP}
	echo ${HETS_BASEDIR}/desktop
	echo ${SEP}
	ls -al ${HETS_BASEDIR}/desktop
	echo ${SEP}
}

function myShowCacheUsage {
	# keep in sync with 'cache:'
	du -sh ${STACK_ROOT} ${PKG_CACHE} ${HETS_LIB} ${HETS_BASEDIR}
	du -sh ${STACK_ROOT}/* ${HETS_BASEDIR}/* 2>/dev/null
	return 0
}

function myWaitForJob {
	local WJOB="$1" X
	SECONDS=0
	local TIMEOUT=300
	if [[ -f /tmp/timestamp ]]; then
		X=$(</tmp/timestamp)
		if (( X > 0 )); then
			N=`ksh -c 'printf "%(%s)T" now'`
			# Assume it has been alread running for ~ 3 min and reserve 5 min
			# for cache upload
			(( TIMEOUT = 50 * 60 - (N - X) - 180 - 300 ))
			(( TIMEOUT < 60 )) && TIMEOUT=60
		fi
	fi
	echo "Job ${TRAVIS_JOB_NUMBER} is waiting for ${WJOB} ..."
	while : ; do
		if curl -so /tmp/${WJOB} "${PULL_URL}/${TRAVIS_BUILD_NUMBER}.0/${WJOB}"
		then
			X=$(</tmp/${WJOB})
			[[ $X == '1' || $X == '0' ]] && return $X
		fi
		(( SECONDS > TIMEOUT )) && break
		printf '.'
		sleep 10
	done
	echo 'Giving up - no sync info after 5 min.'
	return 99
}

# stuff to call in each job's "before_cache" hook
function myBefore_cache {
	# no need to check for changes (0..1min) nor to targz and upload the whole
	# cache (~ 2..4.5 min) after testing => saves over all ~ 11 min
	if [[ ${TRAVIS_BUILD_STAGE_NAME} == "Test" ]]; then
		rm -f ${CASHER_DIR}/bin/casher
		return 0
	fi

	local X
	[[ ${JOB_NAME} =~ ^(server|pg)$ ]] && X='server' || X='desktop'

	rm -rf ${STACK_ROOT:-~/empty}/programs/x86_64-linux/*/share/doc
	rm -rf ${HETS_BUILD_DIR}/{hets.bin,hets_server.bin,hets,hets_server}
	[[ -d ${HETS_BASEDIR}/$X ]] && \
		mv ${HETS_BASEDIR}/$X ${HETS_BASEDIR}/${X}.old
	mv ${HETS_BUILD_DIR} ${HETS_BASEDIR}/$X
	[[ -z "${SMART_CACHE}" ]] && rm -rf ${HETS_BASEDIR}/${X}.old && return 0

	if [[ ${TRAVIS_EVENT_TYPE} == 'push' ]]; then
		# on 'push' we just want to keep the Stack cache
		if [[ ${TRAVIS_BUILD_STAGE_NAME} == 'Stack' ]]; then
			mv ${HETS_BASEDIR}/$X/.stack-work ${HETS_BASEDIR}/
			rm -rf ${HETS_BASEDIR}/*
			mkdir ${HETS_BASEDIR}/$X
			mv ${HETS_BASEDIR}/.stack-work ${HETS_BASEDIR}/$X/
		else
			rm -f ${CASHER_DIR}/bin/casher
		fi
		return 0
	fi

	if [[ ${TRAVIS_BUILD_STAGE_NAME} == 'Stack' ]]; then
		[[ -e /tmp/update.stack ]] || rm -f ${CASHER_DIR}/bin/casher
		return 0
	fi

	if [[ ${TRAVIS_BUILD_STAGE_NAME} != 'Build' ]]; then
		echo "Nothing to do for '${TRAVIS_BUILD_STAGE_NAME}'."
		return 0
	fi

	local NEED_PUSH L
	if [[ ${JOB_NAME} == 'server' ]]; then
		SECONDS=0
		echo 'Upload check ...'
		if [[ -d ${HETS_BASEDIR}/${X}.old ]]; then
			rsync -n --del -rlpmucv --exclude='.stack-work' \
				${HETS_BASEDIR}/$X/ ${HETS_BASEDIR}/${X}.old/ >/tmp/nsync
			L=`cat /tmp/nsync | wc -l`
			echo "$L changes:"
			(( L < 200 )) && cat /tmp/nsync || head -100 /tmp/nsync
			(( L > 4 )) && NEED_PUSH=1 || NEED_PUSH=0
		else
			NEED_PUSH=1
		fi
		if (( NEED_PUSH )); then
			cd ${HETS_BASEDIR}
			tar cplzf ${X}.tgz $X
			curl -q --no-remote-time -F "job=${TRAVIS_BUILD_NUMBER}.0" \
				-F 'button=1' -F "upfile=@${X}.tgz" ${PUSH_URL}
		fi
		echo "${NEED_PUSH}" >/tmp/$X
		curl -q --no-remote-time -F "job=${TRAVIS_BUILD_NUMBER}.0" \
			-F 'button=1' -F "upfile=@/tmp/$X" ${PUSH_URL}
		rm -f ${CASHER_DIR}/bin/casher
		echo "done (${SECONDS} s)."
		return 0
	fi

	# Wait for the server to finish
	myWaitForJob server
	local RES=$?
	if (( RES == 1 )); then
		echo 'Syncing hets_server ...'
		SECONDS=0
		if curl -s --no-remote-time -o /tmp/server.tgz \
			"${PULL_URL}/${TRAVIS_BUILD_NUMBER}.0/server.tgz"
		then
			rm -rf ${HETS_BASEDIR}/server
			cd ${HETS_BASEDIR}
			tar xzf /tmp/server.tgz
			echo "done (${SECONDS} s)."
		else
			echo 'failed.'
		fi
	else
		(( RES == 0 )) && echo 'No sync wrt. hets_server required.' || \
			echo 'Unable to sync with hets_server.'
		if [[ -d ${HETS_BASEDIR}/${X}.old ]]; then
			rsync -n --del -rlpmucv --exclude='.stack-work' \
				${HETS_BASEDIR}/$X/ ${HETS_BASEDIR}/${X}.old/ >/tmp/nsync
			L=`cat /tmp/nsync | wc -l`
			echo "$L changes:"
			(( L < 200 )) && cat /tmp/nsync || head -100 /tmp/nsync
			(( L > 4 )) || rm -f ${CASHER_DIR}/bin/casher	# no changes
		fi
	fi
	rm -rf ${HETS_BASEDIR}/${X}.old

	return 0
}

# if STACK_ROOT is set, download if not yet available
function myCheckStack {
	[[ -z "${STACK_ROOT}" ]] && return 0
	[[ -e ${STACK_ROOT}/bin/stack.done ]] || touch /tmp/update.stack
	[[ -x ${STACK_ROOT}/bin/stack ]] && return 0
	[[ -d ${STACK_ROOT}/bin ]] || mkdir -p ${STACK_ROOT}/bin
	curl --retry 3 --retry-delay 10 -L \
		https://www.stackage.org/stack/linux-x86_64 | \
		tar xz --wildcards --strip-components=1 -C ${STACK_ROOT}/bin '*/stack'
}

function myGetMissingPkgs {
	# if stack has already been build, we can skip this for stage 'Stack'
	# because even if the packages are in the cache, extraction alias
	# installation still takes ~ 90s and make stack 
	[[ "${TRAVIS_BUILD_STAGE_NAME}" == 'Stack' && -n "${STACK_ROOT}" \
		&& -x ${STACK_ROOT}/bin/stack && -e ${STACK_ROOT}/bin/stack.done ]] && \
		return 0
	which rsync || apt-get install rsync

	# we do not need any packages from there - reduce apt-get update time
	sudo rm -f /etc/apt/sources.list.d/{computology_apt-backport,docker,git-ppa,github_git-lfs,heroku-toolbelt,pollinate}.list
	# DB tests require PostgreSQL 9.5+ because of 'CREATE INDEX IF NOT EXISTS'
	# and xenial is the 1st release, which ships it
	sudo rm -f /etc/apt/sources.list.d/pgdg.list

	# utilize cached packages
	sudo apt-get update
	if [[ -n "${PKG_CACHE}" ]]; then
		echo 'Copying *.deb from pkg cache ...'
		SECONDS=0
		sudo rsync -ptvu --size-only ${PKG_CACHE}/*.deb /var/cache/apt/archives
		echo "done in ${SECONDS}s."
	fi

	local ADD_PKGS MISSING
	# we want JDK 8 (and remove it from debian build deps)
	ADD_PKGS='openjdk-8-jdk-headless'
	ADD_PKGS+=' spass darwin '

	MISSING+=`dpkg-checkbuilddeps debian/control 2>&1 | \
		sed -e 's/.*dependencies\:\ //' -e 's,([^)]*),,g' \
			-re 's,openjdk-.*-jdk(-headless)?,,'`
	if (( NO_DOCS )); then
		# skip tex packages
		MISSING=`echo "${MISSING}" | sed -re 's/ [-a-z]*?tex[-a-z]+//g'`
	fi
	if [[ -z "${STACK_ROOT}" ]]; then
		ADD_PKGS+=" ${MISSING}"
	else
		ADD_PKGS+=`echo "${MISSING}" | \
			sed -re 's/libghc-[^ ]*( |$)//g' -e 's/ghc|happy|ghc-[^ ]+ //g'`
		ADD_PKGS+=' gcc libgmp-dev libpango1.0-dev libgtk2.0-dev libglade2-dev'
		ADD_PKGS+=' libpq-dev libncurses5-dev'
	fi
	if [[ ${JOB_NAME} == 'pg' ]]; then
		if ! which pg_ctl ; then
			ADD_PKGS+=' postgresql'
		fi
	fi
	echo "Add. Packages: '${ADD_PKGS}' ..."
	SECONDS=0
	sudo apt-get install --no-install-recommends ${ADD_PKGS}
	if [[ ${JOB_NAME} == 'haddock' ]]; then
		# travis-ci uses outdated, broken packages which prevent npm install
		sudo apt --fix-broken install
		sudo apt-get install npm || true
	fi
	echo "fetched in ${SECONDS}s."

	# cache packages
	if [[ -n "${PKG_CACHE}" ]]; then
		echo 'Copying *.deb to pkg cache ...'
		SECONDS=0
		rsync -ptvu --size-only /var/cache/apt/archives/*.deb ${PKG_CACHE}
		echo "done in ${SECONDS}s."
	fi
	# also ensures, that add. packages got installed
	ksh93 -c 'print ${.sh.version}' 2>/dev/null
}

# Hets-lib are required for testing (but not to build)
function myCheckHetslib {
	if [[ -d ${HETS_LIB}/.git ]]; then
		cd ${HETS_LIB}
		git pull
		cd -
	else
		git clone --depth=1 https://github.com/spechub/Hets-lib.git ${HETS_LIB}
	fi
}

# Patch https://raw.githubusercontent.com/travis-ci/casher/master/bin/casher
# to show the URLs used
function myTravisPatch {
	# see also: ~travis/build.sh
	# travis_run_setup_cache()   travis_run_setup_casher() travis_run_cache()
	sed -i.orig -e '/fetching/ s/%r.*/url}"/' \
		-e '/uploading/ s/archive.*/archive to #{url}"/' \
		${CASHER_DIR}/bin/casher
	return 0
}

# X-fer the given files to our own server for inspection/troubleshooting
function myUpload {
	local F FILES=`ls ${HOME}/.casher/{fetch.tgz,md5sums_before,paths}`
	FILES+=" ${HOME}/build.sh ${HOME}/.travis/job_stages"
	ls -alR ${HOME} >/tmp/home.lsR && FILES+=" /tmp/home.lsR"
	tar cplzf /tmp/apt.tgz /etc/apt && FILES+=" /tmp/apt.tgz"
	if (( 0 )); then
		sudo tar cplzf /tmp/pg.tgz /var/lib/postgresql && FILES+=" /tmp/pg.gz "
		FILES+=`ls /var/cache/apt/archives/postgresql*`
		if [[ -d /etc/postgresql ]]; then
			sudo tar cplzf /tmp/pg-etc.tgz /etc/postgresql && \
				FILES+=" /tmp/pg-etc.gz"
		fi
		if [[ -d /var/ramfs/postgresql ]]; then
			sudo tar cplzf /tmp/pg-ramfs.tgz /var/ramfs/postgresql && \
				FILES+=" /tmp/pg-ramfs.gz"
		fi
	fi
	for F in ${FILES} ; do
		echo "Pushing $F ..."
		curl -s --no-remote-time -F "job=${TRAVIS_JOB_NUMBER}" -F 'button=1' \
			-F "upfile=@$F" ${PUSH_URL}
	done
	return 0
}

function myUploadDocs {
	# Just make sure, that we upload docs only on a master merge to save
	# some time and space on the remote store.
	[[ ${TRAVIS_BRANCH} != 'master' || ${TRAVIS_EVENT_TYPE} != 'push' ]] && \
		return 0

	local F="/tmp/docs.tgz"
	if [[ ! -d docs ]] ; then
		echo 'docs/ unavailable - skipping upload.'
		return 0
	fi
	env >docs/.env
	# convert the README.md into docs/README.html
	if [[ -x /usr/bin/npm ]]; then
		npm install --only=production --no-optional marked commander
		utils/md2html.js -t 'Hets (The heterogeneous tool set)' -i README.md \
			-o docs/README.html
		[[ -s docs/README.html ]] || rm -f docs/README.html
	else
		echo 'npm not installed - skipping docs/README.html.'
	fi
	# archive
	if ! tar cplzf $F docs ; then
		echo 'Archiving docs/ failed - skipping upload.'
		return 0
	fi
	# and upload
	curl -q --no-remote-time -F "job=${TRAVIS_BUILD_NUMBER}.0" \
		-F 'button=1' -F "upfile=@$F" ${PUSH_URL}
	return 0
}

function myPrepareBuildDir {
	local X
	[[ ${JOB_NAME} =~ ^(server|pg)$ ]] && X='server' || X='desktop'

	[[ -e ${HETS_BUILD_DIR} ]] && rm -rf ${HETS_BUILD_DIR}

	# we need -c to make sure, we do not miss a file and to not get fooled
	# by wrong, i.e. newer timestamps
	local ARGS=( '-rlpmuc'						# savings
		'--exclude=.git'					# 253M
		'--exclude=OcamlTools'				#  32M
		'--exclude=lib'						#  20M
		'--exclude=hets-mmt-standalone.jar'	#  12M
		'--exclude=Termination'				#   6M
			# ==> ~ 330/358 ~= 93% of the cloned Hets w/o make artifacts
	)
	(( NO_DOCS > 0 )) && ARGS+=( '--exclude=doc' )	#   7M

	if [[ -d ${HETS_BASEDIR}/$X ]]; then
		mv ${HETS_BASEDIR}/$X ${HETS_BUILD_DIR}
		if (( MKDBG )) && \
			[[ ${JOB_NAME} == 'server' || ${JOB_NAME} == 'desktop' ]]
		then
			cd ${HETS_BUILD_DIR}/..
			tar cplzf build-pre.tgz ${HETS_BUILD_DIR}
			curl -q --no-remote-time -F "job=${TRAVIS_JOB_NUMBER}" \
				-F 'button=1' -F "upfile=@build-pre.tgz" ${PUSH_URL}
			rm -f build-pre.tgz
			cd -
		fi
		echo "Syncing ${HETS_BUILD_DIR} ..."
		ARGS+=( '-v' )
		rsync ${ARGS[@]} ${TRAVIS_BUILD_DIR}/ ${HETS_BUILD_DIR}/ | \
			sed -e '/\/$/ d'
		if (( MKDBG )) && \
			[[ ${JOB_NAME} == 'server' || ${JOB_NAME} == 'desktop' ]]
		then
			cd ${HETS_BUILD_DIR}/..
			tar cplzf build-post.tgz ${HETS_BUILD_DIR}
			curl -q --no-remote-time -F "job=${TRAVIS_JOB_NUMBER}" \
				-F 'button=1' -F "upfile=@build-post.tgz" ${PUSH_URL}
			rm -f build-post.tgz
			cd -
		fi
	else
		echo "Copying Hets to ${HETS_BUILD_DIR} ..."
		mkdir ${HETS_BUILD_DIR}
		rsync ${ARGS[@]} ${TRAVIS_BUILD_DIR}/ ${HETS_BUILD_DIR}/
	fi
	ARGS='OWL2/java/lib'
	[[ -e ${HETS_BUILD_DIR}/${ARGS} ]] || \
		ln -s ${TRAVIS_BUILD_DIR}/${ARGS} ${HETS_BUILD_DIR}/${ARGS}

	if [[ ! -d ${HETS_BUILD_DIR}/doc ]]; then
		# do not build
		mkdir ${HETS_BUILD_DIR}/doc
		touch ${HETS_BUILD_DIR}/doc/UserGuide.pdf
	fi
	if [[ $X == 'server' ]]; then
		[[ -d ${HETS_BUILD_DIR}/.stack-work ]] || \
			cp -a ${HETS_BASEDIR}/desktop/.stack-work ${HETS_BUILD_DIR}/
	fi
	# required to make final upload decision - costs 2-3 s, only but usually
	# saves 2.5..3 min.
	if [[ -n "${SMART_CACHE}" ]]; then
		 [[ ${JOB_NAME} == 'server' || ${JOB_NAME} == 'desktop' ]] && \
			cp -a ${HETS_BUILD_DIR} ${HETS_BASEDIR}/$X
	fi
	return 0
}

function myShutdownPgDB {
	[[ ${TRAVIS_INIT} == 'upstart' ]] && sudo service postgresql stop || \
		sudo systemctl stop postgresql
}

"$@"
