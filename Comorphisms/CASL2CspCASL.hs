{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to CspCASL.
-}

module Comorphisms.CASL2CspCASL where

import Logic.Logic
import Logic.Comorphism

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- CspCASL
import CspCASL.Logic_CspCASL
import CspCASL.AS_CspCASL (CspBasicSpec (..), CspCASLSentence, emptyCCSentence)
import CspCASL.SignCSP

-- | The identity of the comorphism
data CASL2CspCASL = CASL2CspCASL deriving (Show)

instance Language CASL2CspCASL -- default definition is okay

instance Comorphism CASL2CspCASL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol Q_ProofTree
               CspCASL ()
               CspBasicSpec CspCASLSentence SYMB_ITEMS SYMB_MAP_ITEMS
               CspCASLSign
               CspMorphism
               () () () where
    sourceLogic CASL2CspCASL = CASL
    sourceSublogic CASL2CspCASL = SL.top
    targetLogic CASL2CspCASL = CspCASL
    mapSublogic CASL2CspCASL _ = Just ()
    map_theory CASL2CspCASL = return . simpleTheoryMapping mapSig mapSen
    map_morphism CASL2CspCASL = return . mapMor
    map_sentence CASL2CspCASL _sig = return . mapSen -- toSentence sig
    -- this function has now the error implementation as default
    -- map_symbol = errMapSymbol -- Set.singleton . mapSym
    has_model_expansion CASL2CspCASL = True
    is_weakly_amalgamable CASL2CspCASL = True
    isInclusionComorphism CASL2CspCASL = True

mapSig :: CASLSign -> CspCASLSign
mapSig sign =
     (emptySign emptyCspSign) {sortSet = sortSet sign
               , sortRel = sortRel sign
               , opMap = opMap sign
               , assocOps = assocOps sign
               , predMap = predMap sign }

mapMor :: CASLMor -> CspMorphism
mapMor m =
  (embedMorphism emptyCspAddMorphism (mapSig $ msource m) $ mapSig $ mtarget m)
  { sort_map = sort_map m
  , fun_map = fun_map m
  , pred_map = pred_map m }

mapSen :: CASLFORMULA -> CspCASLSentence
mapSen _ = emptyCCSentence
