{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, 
 FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Comorphisms/CASL2VSE.hs
Description :  embedding from CASL to VSE
Copyright   :  (c) C. Maeder, DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to VSE.
-}

module Comorphisms.CASL2VSE (CASL2VSE (..)) where

import qualified Data.HashSet as Set

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

import VSE.Logic_VSE
import VSE.As
import VSE.Ana

import Common.ProofTree

import GHC.Generics (Generic)
import Data.Hashable

-- | The identity of the comorphism
data CASL2VSE = CASL2VSE deriving (Show, Generic)

instance Hashable CASL2VSE

instance Language CASL2VSE -- default definition is okay

instance Comorphism CASL2VSE
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
    sourceLogic CASL2VSE = CASL
    sourceSublogic CASL2VSE = SL.cFol
    targetLogic CASL2VSE = VSE
    mapSublogic CASL2VSE _ = Just ()
    map_theory CASL2VSE = return . embedCASLTheory emptyProcs
    map_morphism CASL2VSE = return . mapCASLMor emptyProcs emptyMorExt
    map_sentence CASL2VSE _ = return . mapFORMULA
    map_symbol CASL2VSE _ = Set.singleton . id
    has_model_expansion CASL2VSE = True
    is_weakly_amalgamable CASL2VSE = True
    isInclusionComorphism CASL2VSE = True
