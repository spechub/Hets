{- |
Module      :  $Header$
Description :  Coding of Propositional into CASL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Propositional to CASL.
-}

module Comorphisms.Prop2CASL
    (
     Prop2CASL (..)
    )
    where

import Common.ProofTree

import Logic.Logic
import Logic.Comorphism

-- Propositional
import qualified Propositional.Logic_Propositional as PLogic
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor
import Propositional.Prop2CASLHelpers

-- | lid of the morphism
data Prop2CASL = Prop2CASL deriving Show

instance Language Prop2CASL where
  language_name Prop2CASL = "Propositional2CASL"

instance Comorphism Prop2CASL
    PLogic.Propositional
    PSL.PropSL
    PBasic.BASIC_SPEC
    PBasic.FORMULA
    PBasic.SYMB_ITEMS
    PBasic.SYMB_MAP_ITEMS
    PSign.Sign
    PMor.Morphism
    PSymbol.Symbol
    PSymbol.Symbol
    ProofTree
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
      sourceLogic Prop2CASL = PLogic.Propositional
      sourceSublogic Prop2CASL = PSL.top
      targetLogic Prop2CASL = CLogic.CASL
      mapSublogic Prop2CASL = Just . mapSub
      map_theory Prop2CASL = mapTheory
      is_model_transportable Prop2CASL = True
      map_symbol Prop2CASL _ = mapSym
      map_sentence Prop2CASL = mapSentence
      map_morphism Prop2CASL = mapMor
      has_model_expansion Prop2CASL = True
      is_weakly_amalgamable Prop2CASL = True
      isInclusionComorphism Prop2CASL = True
