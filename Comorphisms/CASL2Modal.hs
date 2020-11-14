{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2Modal.hs
Description :  embedding from CASL to ModalCASL
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to ModalCASL.

-}

module Comorphisms.CASL2Modal (CASL2Modal (..)) where

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

-- ModalCASL
import Modal.Logic_Modal
import Modal.AS_Modal
import Modal.ModalSign

-- | The identity of the comorphism
data CASL2Modal = CASL2Modal deriving (Show)

instance Language CASL2Modal -- default definition is okay

instance Comorphism CASL2Modal
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               Modal ()
               M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MSign
               ModalMor
               Symbol RawSymbol () where
    sourceLogic CASL2Modal = CASL
    sourceSublogic CASL2Modal = SL.top
    targetLogic CASL2Modal = Modal
    mapSublogic CASL2Modal _ = Just ()
    map_theory CASL2Modal = return . embedCASLTheory emptyModalSign
    map_morphism CASL2Modal = return . mapCASLMor emptyModalSign emptyMorExt
    map_sentence CASL2Modal _ = return . mapFORMULA
    map_symbol CASL2Modal _ = Set.singleton . id
    has_model_expansion CASL2Modal = True
    is_weakly_amalgamable CASL2Modal = True
    isInclusionComorphism CASL2Modal = True
