{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module SegExamples where

import ModalLogic
import CombLogic
import GenericSequent

-- example Segala
test1 = And (At (K (And (At (KD (At (K T)))) F))) (And (And F (At (K F))) F)

test2 = At (K T)
test3 = At (KD F)

test4 = And (At (K T)) (At (K (And F (At (G 2 T))))) -- []T/\[](F/\[2]T)
