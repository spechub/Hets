{-# LINE 1 "Reduce/AS_BASIC_Reduce.der.hs" #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Reduce.Tools where

import Reduce.AS_BASIC_Reduce
import Common.Id

negateFormula :: CMD -> CMD
negateFormula (Cmd s exps) = Cmd "Not" [(Op s exps nullRange)]

