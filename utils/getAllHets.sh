#!/bin/bash

## This script downloads, bunzips daily hets;
## afterwards it adds excutable permissions for everyone

HETS_VER=$1
HETS_TMP=$HOME/tmp/hets_installer
HETS_DOWNLOAD=$HETS_TMP/hets

HETS_LINUX=$HETS_DOWNLOAD/linux/hets-$HETS_VER
HETS_MAC=$HETS_DOWNLOAD/mac/hets-$HETS_VER
HETS_SOL=$HETS_DOWNLOAD/solaris/hets-$HETS_VER

DAILY_HETS_LINUX=$HETS_LINUX.bz2
DAILY_HETS_MAC=$HETS_MAC.bz2
DAILY_HETS_SOL=$HETS_SOL.bz2

if [ -d $HETS_DOWNLOAD ] ;
then rm -fr $HETS_DOWNLOAD/* 2>/dev/null ; 
fi ;

mkdir -p $HETS_DOWNLOAD/linux ; mkdir $HETS_DOWNLOAD/mac; \
                                mkdir $HETS_DOWNLOAD/solaris

ARCH_DIR=""
DOWNLOADCMD_L="wget --output-document=$DAILY_HETS_LINUX"
DOWNLOADCMD_M="wget --output-document=$DAILY_HETS_MAC"
DOWNLOADCMD_S="wget --output-document=$DAILY_HETS_SOL"

DAILY_HETS_URL_LINUX="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/linux/daily/hets.bz2"
DAILY_HETS_URL_MAC="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/mac/daily/hets.bz2"
DAILY_HETS_URL_SOLARIS="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/solaris/daily/hets.bz2"

# main
$DOWNLOADCMD_L $DAILY_HETS_URL_LINUX
#bunzip2 $DAILY_HETS_LINUX
#chmod a+x $HETS_LINUX 

$DOWNLOADCMD_M $DAILY_HETS_URL_MAC
#bunzip2 $DAILY_HETS_MAC
#chmod a+x $HETS_MAC 

$DOWNLOADCMD_S $DAILY_HETS_URL_SOLARIS
#bunzip2 $DAILY_HETS_SOL
#chmod a+x $HETS_SOL

echo "Downloaded and saved daily hets to: " $DAILY_HETS_LINUX
echo "Downloaded and saved daily hets to: " $DAILY_HETS_MAC
echo "Downloaded and saved daily hets to: " $DAILY_HETS_SOL