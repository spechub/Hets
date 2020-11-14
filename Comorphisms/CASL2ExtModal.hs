{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2ExtModal.hs
Description :  embedding from CASL to ExtModal
Copyright   :  (c) C. Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to ExtModal.
-}

module Comorphisms.CASL2ExtModal (CASL2ExtModal (..)) where

import qualified Data.HashSet as Set

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.MorphismExtension
import ExtModal.Sublogic

import Common.ProofTree

-- | The identity of the comorphism
data CASL2ExtModal = CASL2ExtModal deriving Show

instance Language CASL2ExtModal -- default definition is okay

instance Comorphism CASL2ExtModal
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol () where
    sourceLogic CASL2ExtModal = CASL
    sourceSublogic CASL2ExtModal = SL.top
    targetLogic CASL2ExtModal = ExtModal
    mapSublogic CASL2ExtModal s = Just s { ext_features = botSublogic }
    map_theory CASL2ExtModal = return . embedCASLTheory emptyEModalSign
    map_morphism CASL2ExtModal =
      return . mapCASLMor emptyEModalSign emptyMorphExtension
    map_sentence CASL2ExtModal _ = return . mapFORMULA
    map_symbol CASL2ExtModal _ = Set.singleton . id
    has_model_expansion CASL2ExtModal = True
    is_weakly_amalgamable CASL2ExtModal = True
    isInclusionComorphism CASL2ExtModal = True
