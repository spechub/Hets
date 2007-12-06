{- |
Module      :  $Header$
Description :  a dummy implementation, so far
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a dummy comorphism
-}

module Comorphisms.OWL2CASL where

import Logic.Logic
import Logic.Comorphism
import CASL.Logic_CASL
import OWL.Logic_OWL11
import OWL.AS
import OWL.Sign
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Morphism

-- | The identity of the comorphism
data OWL2CASL = OWL2CASL deriving Show

instance Language OWL2CASL -- default definition is okay

instance Comorphism OWL2CASL
               OWL11 ()
               Ontology Sentence () ()
               OWL.Sign
               OWL_DLMorphism
               () () ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol () where
  sourceLogic OWL2CASL = OWL11
  targetLogic OWL2CASL = CASL
