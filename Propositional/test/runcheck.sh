#!/bin/ksh93

#first parameter is executable
#second parameter resets ouput files

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

${SD}/TestSublogic || addErr

(( ! ERR ))
