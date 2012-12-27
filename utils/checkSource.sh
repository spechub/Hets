#!/bin/sh

for f in $@
do
 $HOME/.cabal/bin/scan $f
 $HOME/.cabal/bin/hlint -i "Use camelCase" -i "Use infix" \
    -i "Use >=>" -i "Use first" -i "Use ***" -i "Use second" -i "Use &&&" $f
done
