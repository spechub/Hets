{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  generic CspCASL instance for comorphisms
Copyright   :  (c) Liam O'Reilly, Swansea University 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  experimental
Portability :  non-portable(import Logic.Logic)

-}

module CspCASL.Comorphisms where

import Logic.Logic
import Logic.Comorphism

-- CspCASL
import CspCASL.AS_CspCASL (CspBasicSpec (..))
import CspCASL.Morphism
import CspCASL.Logic_CspCASL
import CspCASL.SignCSP
import CspCASL.SymbItems
import CspCASL.Symbol

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
      CspBasicSpec CspCASLSen CspSymbItems CspSymbMapItems
        CspCASLSign CspCASLMorphism CspSymbol CspRawSymbol ()
    (GenCspCASL b) ()
      CspBasicSpec CspCASLSen CspSymbItems CspSymbMapItems
        CspCASLSign CspCASLMorphism CspSymbol CspRawSymbol () where
    sourceLogic (CspCASL2CspCASL a _) = GenCspCASL a
    sourceSublogic _ = ()
    targetLogic (CspCASL2CspCASL _ b) = GenCspCASL b
    mapSublogic _ _ = Just ()
    map_theory _ = return
    map_morphism _ = return
    map_sentence _ = const return
    map_symbol _ _ = Set.singleton
    is_model_transportable _ = True
    has_model_expansion _ = True
    is_weakly_amalgamable _ = True
    isInclusionComorphism _ = True
