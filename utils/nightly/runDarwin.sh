#!/bin/sh

for i in $*
do
  echo $i
  time darwin -fd true -pmtptp true -to 10 $i | fgrep "SZS status"
  mv $i $i.fin
done
