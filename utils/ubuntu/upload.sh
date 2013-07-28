#!/bin/bash

function codename {
	(
		source /etc/*-release
		echo $DISTRIB_CODENAME
	)
}

#taken from https://wiki.ubuntu.com/DevelopmentCodeNames
function codenames {
	echo "lucid precise"
}

function modify_changelog {
	e Patching "$SCRIPT_PATH/packages/$PKG/debian/changelog"
	grep -q ") $1; urgency=low" "$SCRIPT_PATH/packages/$PKG/debian/changelog"
	if [ $? -ne 0 ]; then
		e "Can't patch. Make sure the file contains" '"' \
		 ") $1; urgency=low" '"'
		exit 1
	fi
	sed -i "s/) $1; urgency=low/~$2) $2; urgency=low/g" \
	 "$SCRIPT_PATH/packages/$PKG/debian/changelog"
}

function build_with_source {
	e "Building with source"
	debuild -S -sa
	if [ $? -ne 0 ]; then
		e "Build failed"
		exit 1
	fi
}

function build_without_source {
	e "Building without source"
	debuild -S -sd
	if [ $? -ne 0 ]; then
                e "Build failed"
		exit 1
        fi
}

function upload {
	e "Uploading"
	dput ppa:hets/hets $SCRIPT_PATH/packages/*.changes
	if [ $? -ne 0 ]; then
                e "Upload failed"
		exit 1
        fi
}

function git_clean {
	e "Cleaning up $SCRIPT_PATH/packages/"
	git clean -df "$SCRIPT_PATH/packages/" > /dev/null
	git checkout "$SCRIPT_PATH/packages/" > /dev/null
}

function extract_source {
	e "Extracting source archive $SCRIPT_PATH/$PKG.archive"
        tar -C "$SCRIPT_PATH/packages/" -xaf "$SCRIPT_PATH/$PKG.archive"
	if [ $? -ne 0 ]; then
                e "Extract failed!"
                exit 1
        fi
}

function e {
	echo "---" $@
}

export PKG=$1
export SCRIPT_PATH=$PWD

if [ -f "$SCRIPT_PATH/packages/$PKG.info" ]; then
	source "$SCRIPT_PATH/packages/$PKG.info"
	if [ \! -f "$SCRIPT_PATH/$PKG.archive" ]; then
		e "Downloading source archive"
		wget -nv -O "$SCRIPT_PATH/$PKG.archive" $PKG_URL
	fi
	if [ \! -f "$SCRIPT_PATH/$PKG.archive" ]; then
		echo "Downlaod failed!"
		exit 1
	fi
	export BUILD_WITHOUT_SOURCE="no"
	for codename in `codenames`
	do
		git_clean
		modify_changelog "$PKG_DISTRO" "$codename"
		extract_source
		cp "$SCRIPT_PATH/$PKG.archive" \
		 "$SCRIPT_PATH/packages/${PKG_NAME}_$PKG_VERSION.orig$PKG_SOURCE_EXT"
		if [ "no" = "$BUILD_WITHOUT_SOURCE" ]; then
			export BUILD_WITHOUT_SOURCE="yes"
		(
			cd "$SCRIPT_PATH/packages/$PKG"
			build_with_source
		) else
		(
			cd "$SCRIPT_PATH/packages/$PKG"
			build_without_source
		)
		fi
		if [ $? -ne 0 ]; then
			exit 1
		fi
		upload
	done
else
	echo "Couldn't find package $PKG"
fi
