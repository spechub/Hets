#!/bin/bash

for i in `find . -name \*.hs -exec fgrep -l \$Header\$ '{}' \;` 
do
   perl -lp -i -e 's+\$Header\$'"+$i+g" $i
done
