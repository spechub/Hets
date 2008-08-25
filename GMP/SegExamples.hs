module SegExamples where

import AbstractSyntax
import GenericSequent

-- example Segala
test1 = KD (And (At (K (And (At (S (KD T))) F))) (And F (At (K F)))) 

test2 = K T
test3 = K F
