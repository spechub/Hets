#!/bin/bash

## This script downloads, bunzips daily hets;
## afterwards it adds excutable permissions for everyone

HETS_VER=$1

HETS_LINUX=$HOME/bin/hets/linux/hets-$HETS_VER
HETS_MAC=$HOME/bin/hets/mac/hets-$HETS_VER
HETS_SOL=$HOME/bin/hets/solaris/hets-$HETS_VER

DAILY_HETS_LINUX=$HETS_LINUX.bz2
DAILY_HETS_MAC=$HETS_MAC.bz2
DAILY_HETS_SOL=$HETS_SOL.bz2



if [ -d $HOME/bin/hets ] ; 
then rm $HETS_LINUX $HETS_MAC $HETS_SOL \
        $DAILY_HETS_TARGET_L $DAILY_HETS_TARGET_M $DAILY_HETS_TARGET_S 2>/dev/null ; 
else mkdir $HOME/bin/hets ; mkdir $HOME/bin/hets/linux ; \
     mkdir $HOME/bin/hets/mac ; mkdir $HOME/bin/hets/solaris     ;
fi

ARCH_DIR=""
DOWNLOADCMD_L="wget --output-document=$DAILY_HETS_LINUX"
DOWNLOADCMD_M="wget --output-document=$DAILY_HETS_MAC"
DOWNLOADCMD_S="wget --output-document=$DAILY_HETS_SOL"

case `uname -s` in
    SunOS) case `uname -p` in
	       sparc) ARCH_DIR=solaris ;;
               *) echo "Unsupported SunOS processor: " `uname -p`
	          exit 2;;
           esac;;
    *inux) case `uname -p` in
               i*86) ARCH_DIR=linux ;;
	       athlon) ARCH_DIR=linux ;;
	       *) echo "Unsupported Linux processor: " `uname -p`
	          exit 2;;
	   esac;;
    Darwin) case `uname -p` in
               powerpc) ARCH_DIR=mac 
	                DOWNLOADCMD_L="ftp -o $DAILY_HETS_TARGET_L"
			DOWNLOADCMD_M="ftp -o $DAILY_HETS_TARGET_M"
			DOWNLOADCMD_S="ftp -o $DAILY_HETS_TARGET_S" ;;
	       *86) ARCH_DIR=mac ;;
	       *) echo "Unsupported Mac OS X processor: " `uname -p`
	          exit 2;;
            esac;;
    *) echo "Unsupported system: " `uname -s`
       exit 2;;
esac
DAILY_HETS_URL_LINUX="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/linux/daily/hets.bz2"
DAILY_HETS_URL_MAC="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/mac/daily/hets.bz2"
DAILY_HETS_URL_SOLARIS="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/solaris/daily/hets.bz2"

# main
$DOWNLOADCMD_L $DAILY_HETS_URL_LINUX
$DOWNLOADCMD_M $DAILY_HETS_URL_MAC
$DOWNLOADCMD_S $DAILY_HETS_URL_SOLARIS

bunzip2 $DAILY_HETS_LINUX
chmod a+x $HETS_LINUX 

bunzip2 $DAILY_HETS_MAC
chmod a+x $HETS_MAC 

bunzip2 $DAILY_HETS_SOL
chmod a+x $HETS_SOL

echo "Downloaded and saved daily hets to: " $DAILY_HETS_LINUX
echo "Downloaded and saved daily hets to: " $DAILY_HETS_MAC
echo "Downloaded and saved daily hets to: " $DAILY_HETS_SOL