#!/usr/local/bin/bash

for i in MixIds Terms Formula SortItem OpItem PredItem BasicSpec;
do
    echo testing $i
    capa $i $i.casl >& temp
    fgrep -s "parse error" temp || echo " " passed
    diff temp $i.casl.output >& /dev/null || echo " " $i failed diff
    capa $i Wrong$i.casl >& temp
    wc -l Wrong$i.casl
    fgrep -c "parse error" temp || echo " " Wrong$i failed error grep
    diff temp Wrong$i.casl.output >& /dev/null \
	    || echo " " Wrong$i failed diff
done

#extra test
echo testing MixIds as Terms
capa Terms MixIds.casl >& temp
fgrep -l "parse error" temp || echo " " passed
diff -w temp MixIds.casl.output >& /dev/null || \
    echo " " MixIds as Terms failed
capa Terms WrongMixIds.casl >& temp
diff temp WrongMixIds.casl.asTerms.output >& /dev/null || \
    echo " " WrongMixIds as Terms failed
