{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
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
import Common.Keywords
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty
import Modal.AS_Modal

		       
data ModalSign = ModalSign { rigidOps :: Map.Map Id (Set.Set OpType)
			   , rigidPreds :: Map.Map Id (Set.Set PredType) 
			   } deriving (Show, Eq)

emptyModalSign :: ModalSign
emptyModalSign = ModalSign Map.empty Map.empty

instance PrettyPrint ModalSign where
    printText0 ga s = 
	ptext rigidS <+> ptext opS <+> commaT_text ga (Map.keys $ rigidOps s)
        $$ 	
	ptext rigidS <+> ptext predS 
		  <+> commaT_text ga (Map.keys $ rigidPreds s)
