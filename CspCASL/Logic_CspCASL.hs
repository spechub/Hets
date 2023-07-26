{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables
  , TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./CspCASL/Logic_CspCASL.hs
Description :  CspCASL instance of type class logic
Copyright   :  (c)  Markus Roggenbach, Till Mossakowski and Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  experimental
Portability :  non-portable(import Logic.Logic)

Here is the place where the class Logic is instantiated for CspCASL.  A
CspCASL signature is a CASL signature with a set of named channels and
processes. Every process has a profile. Morphisms are supposed to allow
renaming of channels and processes, too. Also sublogics (as a superset of some
CASL sublogics) are still missing.
-}

module CspCASL.Logic_CspCASL
  ( GenCspCASL (..)
  , CspCASLSemantics
  , CspCASL
  , cspCASL
  , Trace (..)
  , traceCspCASL
  , Failure (..)
  , failureCspCASL
  ) where

import Logic.Logic
import Logic.Prover

import Common.DocUtils

import CASL.Logic_CASL
import CASL.Parse_AS_Basic
import CASL.Morphism
import CASL.Sign
import CASL.ToDoc
import qualified CASL.MapSentence as MapSen
import qualified CASL.SimplifySen as SimpSen

import CspCASL.ATC_CspCASL ()
import CspCASL.CspCASL_Keywords
import CspCASL.Morphism as CspCASL_Morphism
import CspCASL.Parse_CspCASL ()
import CspCASL.Print_CspCASL ()
import qualified CspCASL.SignCSP as SignCSP
import qualified CspCASL.SimplifySen as SimplifySen
import CspCASL.StatAnaCSP
import CspCASL.SymbItems
import CspCASL.Symbol
import CspCASL.SymMapAna

import CspCASLProver.CspCASLProver (cspCASLProver)

-- | a generic logic id for CspCASL with different semantics
data GenCspCASL a = GenCspCASL a deriving Show

cspCASL :: GenCspCASL ()
cspCASL = GenCspCASL ()

-- | The top-level logic with the loosest semantics (and without provers)
type CspCASL = GenCspCASL ()

instance Show a => Language (GenCspCASL a) where
      language_name (GenCspCASL a) = "CspCASL"
        ++ let s = show a in if s == "()" then "" else '_' : s
      description _ =
        "CspCASL - extension of CASL with the process algebra CSP\n" ++
        "See http://www.cs.swan.ac.uk/~csmarkus/ProcessesAndData/"

-- | Instance of Sentences for CspCASL
instance Show a => Sentences (GenCspCASL a)
    -- sentence
    SignCSP.CspCASLSen
    -- signature
    SignCSP.CspCASLSign
    -- morphism
    CspCASL_Morphism.CspCASLMorphism
    -- symbol
    CspSymbol
    where
      map_sen (GenCspCASL _) m = return . MapSen.mapSen mapSen m
      sym_name (GenCspCASL _) = cspSymName
      symmap_of (GenCspCASL _) = cspMorphismToCspSymbMap
      simplify_sen (GenCspCASL _) =
        SimpSen.simplifySen (const return) SimplifySen.simplifySen
      sym_of (GenCspCASL _) = symSets
      symKind (GenCspCASL _) = show . pretty . cspSymbType
      print_named (GenCspCASL _) = printTheoryFormula

-- | Syntax of CspCASL
instance Show a => Syntax (GenCspCASL a)
    CspBasicSpec -- basic_spec
    CspSymbol
    CspSymbItems
    CspSymbMapItems
    where
      parse_symb_items (GenCspCASL _) = Just . const $ cspSymbItems
      parse_symb_map_items (GenCspCASL _) = Just . const $ cspSymbMapItems
      parse_basic_spec (GenCspCASL _) = Just $ basicSpec startCspKeywords

-- lattices (for sublogics) missing

class Show a => CspCASLSemantics a where
  cspProvers :: a
    -> [Prover SignCSP.CspCASLSign SignCSP.CspCASLSen
        CspCASL_Morphism.CspCASLMorphism () ()]
  cspProvers _ = []

{- further dummy types for the trace of the failure semantics can be added
   and made an instance of CspCASLSemantics.
   "identity" Comorphisms between these different logics still need to be
   defined.
-}

instance CspCASLSemantics ()

data Trace = Trace deriving Show
data Failure = Failure deriving Show

traceCspCASL :: GenCspCASL Trace
traceCspCASL = GenCspCASL Trace

failureCspCASL :: GenCspCASL Failure
failureCspCASL = GenCspCASL Failure

instance CspCASLSemantics Trace where
    cspProvers _ = [cspCASLProver]

instance CspCASLSemantics Failure

-- | Instance of Logic for CspCASL
instance CspCASLSemantics a => Logic (GenCspCASL a)
    -- Sublogics (missing)
    ()
    -- basic_spec
    CspBasicSpec
    -- sentence
    SignCSP.CspCASLSen
    -- symb_items
    CspSymbItems
    -- symb_map_items
    CspSymbMapItems
    -- signature
    SignCSP.CspCASLSign
    -- morphism
    CspCASL_Morphism.CspCASLMorphism
    CspSymbol
    CspRawSymbol
    -- proof_tree (missing)
    ()
    where
      stability (GenCspCASL _) = Testing
      data_logic (GenCspCASL _) = Just (Logic CASL)
      empty_proof_tree _ = ()
      provers (GenCspCASL _) = cspProvers (undefined :: a)

-- | Static Analysis for CspCASL
instance Show a => StaticAnalysis (GenCspCASL a)
    -- basic_spec
    CspBasicSpec
    -- sentence
    SignCSP.CspCASLSen
    -- symb_items
    CspSymbItems
    -- symb_map_items
    CspSymbMapItems
    -- signature
    SignCSP.CspCASLSign
    -- morphism
    CspCASL_Morphism.CspCASLMorphism
    CspSymbol
    CspRawSymbol
    where
      basic_analysis (GenCspCASL _) = Just basicAnalysisCspCASL
      stat_symb_items (GenCspCASL _) = cspStatSymbItems
      stat_symb_map_items (GenCspCASL _) = cspStatSymbMapItems
      id_to_raw (GenCspCASL _) = idToCspRaw
      symbol_to_raw (GenCspCASL _) = ACspSymbol
      matches (GenCspCASL _) = cspMatches

      empty_signature (GenCspCASL _) = SignCSP.emptyCspCASLSign
      is_subsig (GenCspCASL _) = SignCSP.isCspCASLSubSig
      subsig_inclusion (GenCspCASL _) = cspSubsigInclusion
      signature_union (GenCspCASL _) = SignCSP.unionCspCASLSign
      signatureDiff (GenCspCASL _) s = return . diffSig SignCSP.diffCspSig s
      morphism_union (GenCspCASL _) =
          morphismUnion CspCASL_Morphism.cspAddMorphismUnion
                        SignCSP.cspSignUnion

      induced_from_morphism (GenCspCASL _) = cspInducedFromMorphism
      induced_from_to_morphism (GenCspCASL _) = cspInducedFromToMorphism
      cogenerated_sign (GenCspCASL _) = cspCogeneratedSign
      generated_sign (GenCspCASL _) = cspGeneratedSign
