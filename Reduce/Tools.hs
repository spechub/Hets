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


negateFormula :: Cmd -> Cmd
negateFormula s = Cmd "Not" [s]

