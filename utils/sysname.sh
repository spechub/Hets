#!/bin/sh

PATH=/bin/:/usr/bin     # set a safe path

case `uname -s` in
  Linux)  echo linux;;
  SunOS)  echo solaris;;
  Darwin) echo mac;;
  *) echo "unkown architecture";
     exit 2;;
esac
    
