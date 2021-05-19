{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/ExtModal2OWL.hs
Description :  Comorphism from ExtModal to OWL2
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module Comorphisms.ExtModal2OWL where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree

-- OWL = codomain
import OWL2.Logic_OWL2
import OWL2.MS
import Common.IRI
import qualified OWL2.AS as AS
import OWL2.ProfilesAndSublogics
import OWL2.ManchesterPrint ()
import OWL2.Morphism
import OWL2.Symbols
import OWL2.Sign as OS
import OWL2.CASL2OWL

-- ExtModal = domain
import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.Sublogic

import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.Sublogic

data ExtModal2OWL = ExtModal2OWL deriving Show

instance Language ExtModal2OWL

instance Comorphism
    ExtModal2OWL        -- comorphism
    ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
    SYMB_MAP_ITEMS ExtModalSign ExtModalMorph Symbol RawSymbol ()
    OWL2            -- lid codomain
    ProfSub         -- sublogics codomain
    OntologyDocument -- Basic spec codomain
    Axiom           -- sentence codomain
    SymbItems       -- symbol items codomain
    SymbMapItems    -- symbol map items codomain
    OS.Sign         -- signature codomain
    OWLMorphism     -- morphism codomain
    Entity          -- symbol codomain
    RawSymb         -- rawsymbol codomain
    ProofTree       -- proof tree codomain
    where
      sourceLogic ExtModal2OWL = ExtModal
      sourceSublogic ExtModal2OWL = mkTop maxSublogic
      targetLogic ExtModal2OWL = OWL2
      mapSublogic ExtModal2OWL _ = Just topS
      map_theory ExtModal2OWL = mapTheory
