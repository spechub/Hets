#!/bin/bash

## This script downloads, bunzips daily hets;
## afterwards it adds excutable permissions for everyone

DAILY_HETS=$HOME/bin/hets-`date +%F`
DAILY_HETS_WGET_TARGET=$DAILY_HETS".bz2"

if [ -d $HOME/bin ] ; 
then rm $DAILY_HETS $DAILY_HETS_WGET_TARGET ; 
else mkdir $HOME/bin ; 
fi

ARCH_DIR=""
DOWNLOADCMD="wget --output-document=$DAILY_HETS_WGET_TARGET"

case `uname -s` in
    SunOS) case `uname -p` in
	       sparc) ARCH_DIR=solaris ;;
               *) echo "Unsupported SunOS processor: " `uname -p`
	          exit 2;;
           esac;;
    *inux) case `uname -p` in
               i*86) ARCH_DIR=linux ;;
	       *) echo "Unsupported Linux processor: " `uname -p`
	          exit 2;;
	   esac;;
    Darwin) case `uname -p` in
               powerpc) ARCH_DIR=mac 
	                DOWNLOADCMD="ftp -o $DAILY_HETS_WGET_TARGET" ;;
	       *86) ARCH_DIR=mac ;;
	       *) echo "Unsupported Mac OS X processor: " `uname -p`
	          exit 2;;
            esac;;
    *) echo "Unsupported system: " `uname -s`
       exit 2;;
esac
DAILY_HETS_URL="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/$ARCH_DIR/daily/hets.bz2"


# main
$DOWNLOADCMD $DAILY_HETS_URL
bunzip2 $DAILY_HETS_WGET_TARGET
chmod a+x $DAILY_HETS

echo "Downloaded and saved daily hets to: " $DAILY_HETS