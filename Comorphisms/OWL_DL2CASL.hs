{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a dummy comorphism
-}

module Comorphisms.OWL_DL2CASL where

import Logic.Logic
import Logic.Comorphism
import CASL.Logic_CASL
import OWL_DL.Logic_OWL_DL
import OWL_DL.AS
import OWL_DL.Sign
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Morphism

-- | The identity of the comorphism
data OWL_DL2CASL = OWL_DL2CASL deriving Show

instance Language OWL_DL2CASL -- default definition is okay

instance Comorphism OWL_DL2CASL
               OWL_DL ()
               Ontology Sentence () ()
               OWL_DL.Sign.Sign
               OWL_DLMorphism
               () () ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol () where
  sourceLogic OWL_DL2CASL = OWL_DL
  targetLogic OWL_DL2CASL = CASL
