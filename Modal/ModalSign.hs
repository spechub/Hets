{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, C. Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Signatures for modal logic, as extension of CASL signatures.
-}

module Modal.ModalSign where

import CASL.Sign
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Modal.AS_Modal
		       
data ModalSign = ModalSign { rigidOps :: Map.Map Id (Set.Set OpType)
			   , rigidPreds :: Map.Map Id (Set.Set PredType)
			   , modies :: Map.Map SIMPLE_ID [AnModFORM]
			   , termModies :: Map.Map Id [AnModFORM] --SORT
			   } deriving (Show, Eq)

emptyModalSign :: ModalSign
emptyModalSign = ModalSign Map.empty Map.empty Map.empty Map.empty 
