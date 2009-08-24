{- |
Module      :  $Header$
Description :  Coding of Maude with preorder semantics into CASL
Copyright   :  (c) Adri‡n Riesco and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Maude with preorder semantics to CASL.
-}

module Comorphisms.Maude2CASL
    (
     Maude2CASL (..)
    )
    where

import Common.ProofTree

import Logic.Logic
import Logic.Comorphism

-- Maude
import qualified Maude.Logic_Maude as MLogic
import qualified Maude.AS_Maude as MAS
import qualified Maude.Sign as MSign
import qualified Maude.Morphism as MMor
import qualified Maude.Symbol as MSymbol
import qualified Maude.Sentence as MSentence
import Maude.PreComorphism

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

-- | lid of the morphism
data Maude2CASL = Maude2CASL deriving Show

instance Language Maude2CASL where
  language_name Maude2CASL = "Maude2CASL"

instance Comorphism Maude2CASL
    MLogic.Maude
    ()
    MAS.MaudeText
    MSentence.Sentence
    ()
    ()
    MSign.Sign
    MMor.Morphism
    MSymbol.Symbol
    MSymbol.Symbol
    ()
    CLogic.CASL
    CSL.CASL_Sublogics
    CLogic.CASLBasicSpec
    CBasic.CASLFORMULA
    CBasic.SYMB_ITEMS
    CBasic.SYMB_MAP_ITEMS
    CSign.CASLSign
    CMor.CASLMor
    CSign.Symbol
    CMor.RawSymbol
    ProofTree
    where
      sourceLogic Maude2CASL = MLogic.Maude
      sourceSublogic Maude2CASL = ()
      targetLogic Maude2CASL = CLogic.CASL
      mapSublogic Maude2CASL _ = Just CSL.top
      map_theory Maude2CASL = mapTheory
      is_model_transportable Maude2CASL = True
      map_symbol Maude2CASL = mapSymbol
      map_sentence Maude2CASL = mapSentence
      map_morphism Maude2CASL = mapMorphism
      has_model_expansion Maude2CASL = True
      is_weakly_amalgamable Maude2CASL = True
      isInclusionComorphism Maude2CASL = True
