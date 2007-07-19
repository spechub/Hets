#!/bin/sh

../../hets -v2 -o th -n s2 Rename > log 2>&1
svn diff Rename_s2.th
