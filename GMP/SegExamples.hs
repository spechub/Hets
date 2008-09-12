module SegExamples where

import ModalLogic
import CombLogic
import GenericSequent

-- example Segala
test1 = And (At (K (And (At (KD T)) F))) (And (And F (At (K F))) F)

--test4 = 
test2 = At (K T)
test3 = At (KD F)
