#!/usr/local/bin/bash

for i in MixIds Terms Formula SortItem OpItem PredItem BasicSpec;
do
    echo setting $i
    capa $i $i.casl > $i.casl.output
    capa $i Wrong$i.casl > Wrong$i.casl.output
done

capa Terms WrongMixIds.casl > WrongMixIds.casl.asTerms.output


