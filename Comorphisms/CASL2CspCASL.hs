{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2CspCASL.hs
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to CspCASL.
-}

module Comorphisms.CASL2CspCASL where

import Logic.Logic
import Logic.Comorphism
import Common.ProofTree

-- CASL
import CASL.AS_Basic_CASL
import CASL.Logic_CASL
import CASL.Morphism
import CASL.Sign
import CASL.Sublogic as SL

-- CspCASL
import CspCASL.Logic_CspCASL
import CspCASL.StatAnaCSP (CspBasicSpec)
import CspCASL.SignCSP
import CspCASL.Morphism (CspCASLMorphism, emptyCspAddMorphism)
import CspCASL.SymbItems
import CspCASL.Symbol

import qualified Data.Set as Set

-- | The identity of the comorphism
data CASL2CspCASL = CASL2CspCASL deriving (Show)

instance Language CASL2CspCASL -- default definition is okay

instance Comorphism CASL2CspCASL
    CASL CASL_Sublogics CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        CASLSign CASLMor Symbol RawSymbol ProofTree
    CspCASL () CspBasicSpec CspCASLSen CspSymbItems CspSymbMapItems
        CspCASLSign CspCASLMorphism CspSymbol CspRawSymbol () where
    sourceLogic CASL2CspCASL = CASL
    sourceSublogic CASL2CspCASL = SL.top
    targetLogic CASL2CspCASL = cspCASL
    mapSublogic CASL2CspCASL _ = Just ()
    map_theory CASL2CspCASL =
      return . embedCASLTheory emptyCspSign
    map_symbol CASL2CspCASL _ = Set.singleton . caslToCspSymbol
    map_morphism CASL2CspCASL =
      return . mapCASLMor emptyCspSign emptyCspAddMorphism
    map_sentence CASL2CspCASL _sig = return . mapFORMULA
    has_model_expansion CASL2CspCASL = True
    is_weakly_amalgamable CASL2CspCASL = True
    isInclusionComorphism CASL2CspCASL = True
