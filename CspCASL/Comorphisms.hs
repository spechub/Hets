{- |
Module      :  $Header$
Description :  generic CspCASL instance for comorphisms
Copyright   :  (c) Liam O'Reilly, Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  experimental
Portability :  non-portable(import Logic.Logic)

-}

module CspCASL.Comorphisms where

import Logic.Logic
import Logic.Comorphism

-- CASL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- CspCASL
import CspCASL.Logic_CspCASL
import CspCASL.SignCSP
import CspCASL.AS_CspCASL (CspBasicSpec (..))

import qualified Data.Set as Set

-- | The identity of the comorphism
data CspCASL2CspCASL a b = CspCASL2CspCASL a b deriving Show

cspCASLTrace :: CspCASL2CspCASL () Trace
cspCASLTrace = CspCASL2CspCASL () Trace

cspCASLFailure :: CspCASL2CspCASL () Failure
cspCASLFailure = CspCASL2CspCASL () Failure

instance (Show a, Show b) => Language (CspCASL2CspCASL a b) where
  language_name (CspCASL2CspCASL a b) =
      language_name (GenCspCASL a)
      ++ "2" ++ language_name (GenCspCASL b)

instance (CspCASLSemantics a, CspCASLSemantics b)
   => Comorphism (CspCASL2CspCASL a b)
               (GenCspCASL a) ()
               CspBasicSpec CspCASLSen SYMB_ITEMS SYMB_MAP_ITEMS
               CspCASLSign
               CspMorphism
               Symbol RawSymbol ()
               (GenCspCASL b) ()
               CspBasicSpec CspCASLSen SYMB_ITEMS SYMB_MAP_ITEMS
               CspCASLSign
               CspMorphism
               Symbol RawSymbol () where
    sourceLogic (CspCASL2CspCASL a _) = GenCspCASL a
    sourceSublogic _ = ()
    targetLogic (CspCASL2CspCASL _ b) = GenCspCASL b
    mapSublogic _ _ = Just ()
    map_theory _ = return
    map_morphism _ = return
    map_sentence _ = \_ -> return
    map_symbol _ = Set.singleton
    is_model_transportable _ = True
    has_model_expansion _ = True
    is_weakly_amalgamable _ = True
    isInclusionComorphism _ = True
