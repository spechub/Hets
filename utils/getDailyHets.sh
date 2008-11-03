#!/bin/bash

## This script downloads a version of hets (second argument) 
## into a directory (first argument) 
## the daily hets version and your bin directory is used without arguments

if [ -z "$1" ] ; then
   INSTALLDIR="$HOME/bin"
else
   INSTALLDIR="$1"
fi

if [ -z "$2" ] ; then # daily
 TARGET_HETS=hets-`date +%F`
 SOURCE_HETS=daily/hets.bz2
else # version
 TARGET_HETS=hets-$2
 SOURCE_HETS=versions/hets-$2.bz2
fi   

DAILY_HETS=$INSTALLDIR/$TARGET_HETS
DAILY_HETS_TARGET=$DAILY_HETS.bz2

if [ -d "$INSTALLDIR" ] ; then
    if [ -e "$DAILY_HETS" ] ; then
        mv "$DAILY_HETS" "$DAILY_HETS"~
        echo generated backup file: $DAILY_HETS~
    fi
    if [ -e "$DAILY_HETS_TARGET" ] ; then
        rm -f "$DAILY_HETS_TARGET"
        echo removed file: $DAILY_HETS_TARGET
    fi
else
    echo created directory $INSTALLDIR
    mkdir -p "$INSTALLDIR"
fi

ARCH_DIR=""
DOWNLOADCMD="curl -o $DAILY_HETS_TARGET"

case `uname -s` in
    SunOS)
        case `uname -p` in
            sparc)
                ARCH_DIR=solaris ;;
            *86*)
                ARCH_DIR=pc-solaris ;;
            *)
                echo Unsupported SunOS processor: `uname -p`
                exit 2;;
        esac;;
    *inux)
        ARCH_DIR=linux ;;
    Darwin)
        case `uname -p` in
            powerpc)
                ARCH_DIR=mac ;;
            *86)
                ARCH_DIR=intel-mac ;;
            *)
                echo Unsupported Mac OS X processor: `uname -p`
                exit 2;;
        esac;;
    *)
        echo Unsupported system: `uname -s`
        exit 2;;
esac

DAILY_HETS_URL=http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/$ARCH_DIR/$SOURCE_HETS

# main
$DOWNLOADCMD $DAILY_HETS_URL || exit 1
bunzip2 "$DAILY_HETS_TARGET" || exit 1
chmod a+x "$DAILY_HETS" || exit 1

echo "Downloaded and saved daily hets to: " $DAILY_HETS
