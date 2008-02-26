#!/bin/bash

## This script downloads a daily hets into your ~/bin directory

DAILY_HETS=$HOME/bin/hets-`date +%F`
DAILY_HETS_TARGET=$DAILY_HETS.bz2

if [ -d "$HOME/bin" ] ; then
    if [ -e "$DAILY_HETS" ] ; then
        mv $DAILY_HETS "$DAILY_HETS~"
        echo generated backup of exisiting file '"'$DAILY_HETS'"'
    fi
    if [ -e "$DAILY_HETS_TARGET" ] ; then
        rm -f "$DAILY_HETS_TARGET"
        echo removed exisiting file '"'"$DAILY_HETS_TARGET"'"'
    fi
else
    mkdir $HOME/bin
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
                echo "Unsupported SunOS processor: " `uname -p`
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
                echo "Unsupported Mac OS X processor: " `uname -p`
                exit 2;;
        esac;;
    *)
        echo "Unsupported system: " `uname -s`
        exit 2;;
esac

DAILY_HETS_URL=http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/$ARCH_DIR/daily/hets.bz2

# main
$DOWNLOADCMD $DAILY_HETS_URL || exit 1
bunzip2 $DAILY_HETS_TARGET || exit 1
chmod a+x $DAILY_HETS || exit 1

echo "Downloaded and saved daily hets to: " $DAILY_HETS
