{- |
Module      :  $Header$
Description :  embedding from CASL to CoCASL
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to CoCASL.

-}

module Comorphisms.CASL2CoCASL where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import Common.ProofTree

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Fold

-- CoCASLCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import CoCASL.StatAna (CSign)
import CoCASL.Sublogic

-- | The identity of the comorphism
data CASL2CoCASL = CASL2CoCASL deriving (Show)

instance Language CASL2CoCASL -- default definition is okay

instance Comorphism CASL2CoCASL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               CoCASL CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               Symbol RawSymbol () where
    sourceLogic CASL2CoCASL = CASL
    sourceSublogic CASL2CoCASL = SL.top
    targetLogic CASL2CoCASL = CoCASL
    mapSublogic CASL2CoCASL s = Just $ s { ext_features = False }

    map_theory CASL2CoCASL = return . simpleTheoryMapping mapSig mapSen
    map_morphism CASL2CoCASL = return . mapMor
    map_sentence CASL2CoCASL _ = return . mapSen
    map_symbol CASL2CoCASL = Set.singleton . mapSym
    has_model_expansion CASL2CoCASL = True
    is_weakly_amalgamable CASL2CoCASL = True
    isInclusionComorphism CASL2CoCASL = True

mapSig :: CASLSign -> CSign
mapSig sign =
     (emptySign emptyCoCASLSign) {sortSet = sortSet sign
               , sortRel = sortRel sign
               , opMap = opMap sign
               , assocOps = assocOps sign
               , predMap = predMap sign }

mapMor :: CASLMor -> CoCASLMor
mapMor m = (embedMorphism () (mapSig $ msource m) $ mapSig $ mtarget m)
  { sort_map = sort_map m
  , fun_map = fun_map m
  , pred_map = pred_map m }

mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once CoCASL symbols are added

mapSen :: CASLFORMULA -> CoCASLFORMULA
mapSen = foldFormula $ mapRecord (const $ error "CASL2CoCASL.mapSen")
