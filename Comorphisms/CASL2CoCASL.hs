{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2CoCASL.hs
Description :  embedding from CASL to CoCASL
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

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

    map_theory CASL2CoCASL = return . embedCASLTheory emptyCoCASLSign
    map_morphism CASL2CoCASL = return . mapCASLMor emptyCoCASLSign emptyMorExt
    map_sentence CASL2CoCASL _ = return . mapFORMULA
    map_symbol CASL2CoCASL _ = Set.singleton . id
    has_model_expansion CASL2CoCASL = True
    is_weakly_amalgamable CASL2CoCASL = True
    isInclusionComorphism CASL2CoCASL = True
