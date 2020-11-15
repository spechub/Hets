{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, 
 FlexibleInstances, DeriveGeneric #-}
{- |
License     :  GPLv2 or higher, see LICENSE.txt

Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to HybridCASL.

-}

module Comorphisms.CASL2Hybrid (CASL2Hybrid (..)) where

import Logic.Logic
import Logic.Comorphism
import qualified Data.HashSet as Set
import Common.ProofTree
-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- HybridCASL
import Hybrid.Logic_Hybrid
import Hybrid.AS_Hybrid
import Hybrid.HybridSign

import GHC.Generics (Generic)
import Data.Hashable

-- | The identity of the comorphism
data CASL2Hybrid = CASL2Hybrid deriving (Show, Generic)

instance Hashable CASL2Hybrid

instance Language CASL2Hybrid -- default definition is okay

instance Comorphism CASL2Hybrid
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               Hybrid ()
               H_BASIC_SPEC HybridFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               HSign
               HybridMor
               Symbol RawSymbol () where
    sourceLogic CASL2Hybrid = CASL
    sourceSublogic CASL2Hybrid = SL.top
    targetLogic CASL2Hybrid = Hybrid
    mapSublogic CASL2Hybrid _ = Just ()
    map_theory CASL2Hybrid = return . embedCASLTheory emptyHybridSign
    map_morphism CASL2Hybrid = return . mapCASLMor emptyHybridSign emptyMorExt
    map_sentence CASL2Hybrid _ = return . mapFORMULA
    map_symbol CASL2Hybrid _ = Set.singleton . id
    has_model_expansion CASL2Hybrid = True
    is_weakly_amalgamable CASL2Hybrid = True
    isInclusionComorphism CASL2Hybrid = True
