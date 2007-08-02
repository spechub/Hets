#!/bin/bash

## This script downloads, bunzips released hets;

HETS_VER=$1
HETS_TMP=$HOME/tmp/hets_installer
HETS_DOWNLOAD=$HETS_TMP/hets

HETS_LINUX=$HETS_DOWNLOAD/linux/hets-$HETS_VER
HETS_MAC=$HETS_DOWNLOAD/mac/hets-$HETS_VER
HETS_SOL=$HETS_DOWNLOAD/solaris/hets-$HETS_VER
HETS_INTELMAC=$HETS_DOWNLOAD/intel-mac/hets-$HETS_VER

RELEASED_HETS_LINUX=$HETS_LINUX.bz2
RELEASED_HETS_MAC=$HETS_MAC.bz2
RELEASED_HETS_SOL=$HETS_SOL.bz2
RELEASED_HETS_INTELMAC=$HETS_INTELMAC.bz2

if [ -d $HETS_DOWNLOAD ] ;
then rm -fr $HETS_DOWNLOAD/* 2>/dev/null ; 
fi ;

mkdir -p $HETS_DOWNLOAD/linux ; mkdir $HETS_DOWNLOAD/mac; \
           mkdir $HETS_DOWNLOAD/solaris ; mkdir $HETS_DOWNLOAD/intel-mac

ARCH_DIR=""
DOWNLOADCMD_L="wget --output-document=$RELEASED_HETS_LINUX"
DOWNLOADCMD_M="wget --output-document=$RELEASED_HETS_MAC"
DOWNLOADCMD_S="wget --output-document=$RELEASED_HETS_SOL"
DOWNLOADCMD_IM="wget --output-document=$RELEASED_HETS_INTELMAC"


RELEASED_HETS_URL_LINUX="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/linux/releasedhets.bz2"
RELEASED_HETS_URL_MAC="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/mac/releasedhets.bz2"
RELEASED_HETS_URL_SOLARIS="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/solaris/releasedhets.bz2"
RELEASED_HETS_URL_INTELMAC="http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/intel-mac/releasedhets.bz2"

# main
$DOWNLOADCMD_L $RELEASED_HETS_URL_LINUX
#bunzip2 $DAILY_HETS_LINUX
#chmod a+x $HETS_LINUX 

$DOWNLOADCMD_M $RELEASED_HETS_URL_MAC
#bunzip2 $DAILY_HETS_MAC
#chmod a+x $HETS_MAC 

$DOWNLOADCMD_S $RELEASED_HETS_URL_SOLARIS
#bunzip2 $DAILY_HETS_SOL
#chmod a+x $HETS_SOL

$DOWNLOADCMD_IM $RELEASED_HETS_URL_INTELMAC

echo "Downloaded and saved released hets to: " $RELEASED_HETS_LINUX
echo "Downloaded and saved released hets to: " $RELEASED_HETS_MAC
echo "Downloaded and saved released hets to: " $RELEASED_HETS_SOL
echo "Downloaded and saved released hets to: " $RELEASED_HETS_INTELMAC
