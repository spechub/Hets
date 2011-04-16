#!/bin/sh

profile=$HOME"/.bash_profile"

echo "This will add"
echo
cat ./.hets_path
echo
echo "to your "$profile
echo "Are you sure?"
echo "(If unsure, just press enter, else hit Ctrl+C.)"

read var_name
cat ./.hets_path >> $profile
source $profile

