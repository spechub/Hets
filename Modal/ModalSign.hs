{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Signatures for modal logic, as extension of CASL signatures.
-}

data ModalSign = ModalSign { rigidOps :: Map.Map Id (Set.Set OpType)
	       , rigidPred :: Map.Map Id (Set.Set PredType) 
               } deriving Show
