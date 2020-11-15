{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Comorphisms/CspCASL2Modal.hs
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CspCASL to ModalCASL.
   It keeps the CASL part and interprets the CspCASL LTS semantics as
   Kripke structure
-}

module Comorphisms.CspCASL2Modal where

import Logic.Logic
import Logic.Comorphism

-- CASL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- CspCASL
import CspCASL.Logic_CspCASL
import CspCASL.SignCSP
import CspCASL.StatAnaCSP (CspBasicSpec)
import CspCASL.Morphism (CspCASLMorphism)
import CspCASL.SymbItems
import CspCASL.Symbol

-- ModalCASL
import Modal.Logic_Modal
import Modal.AS_Modal
import Modal.ModalSign

import GHC.Generics (Generic)
import Data.Hashable

-- | The identity of the comorphism
data CspCASL2Modal = CspCASL2Modal deriving (Show, Generic)

instance Hashable CspCASL2Modal

instance Language CspCASL2Modal -- default definition is okay

instance Comorphism CspCASL2Modal
    CspCASL () CspBasicSpec CspCASLSen CspSymbItems CspSymbMapItems
        CspCASLSign CspCASLMorphism CspSymbol CspRawSymbol ()
    Modal () M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        MSign ModalMor Symbol RawSymbol () where
    sourceLogic CspCASL2Modal = cspCASL
    sourceSublogic CspCASL2Modal = ()
    targetLogic CspCASL2Modal = Modal
    mapSublogic CspCASL2Modal _ = Just ()
    map_theory CspCASL2Modal = return . embedTheory mapSen emptyModalSign
    map_morphism CspCASL2Modal = return . mapCASLMor emptyModalSign emptyMorExt
    map_sentence CspCASL2Modal _ = return . mapSen

mapSen :: CspCASLSen -> ModalFORMULA
mapSen _ = trueForm
