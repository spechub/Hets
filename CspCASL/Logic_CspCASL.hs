{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables
  , TypeSynonymInstances #-}
{- |
Module      :  $Header$
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

import CASL.Logic_CASL
import CASL.Morphism

import qualified CspCASL.AS_CspCASL as AS_CspCASL
import qualified CspCASL.ATC_CspCASL ()
import CspCASL.Morphism as CspCASL_Morphism
import qualified CspCASL.Parse_CspCASL as Parse_CspCASL
import qualified CspCASL.Print_CspCASL ()
import qualified CspCASL.SignCSP as SignCSP
import qualified CspCASL.SimplifySen as SimplifySen
import CspCASL.StatAnaCSP
import CspCASL.SymbItems
import CspCASL.Symbol

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
        "CspCASL - see\n\n" ++
        "http://www.cs.swan.ac.uk/~csmarkus/ProcessesAndData/"

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
      map_sen (GenCspCASL _) = CspCASL_Morphism.mapSen
      sym_name (GenCspCASL _) = cspSymName
      simplify_sen (GenCspCASL _) = SimplifySen.simplifySen
      sym_of (GenCspCASL _) = symSets

-- | Syntax of CspCASL
instance Show a => Syntax (GenCspCASL a)
    AS_CspCASL.CspBasicSpec -- basic_spec
    CspSymbItems
    CspSymbMapItems
    where
      parse_symb_items (GenCspCASL _) = Just cspSymbItems
      parse_symb_map_items (GenCspCASL _) = Just cspSymbMapItems
      parse_basic_spec (GenCspCASL _) =
          Just Parse_CspCASL.cspBasicSpec

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
    AS_CspCASL.CspBasicSpec
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
      stability (GenCspCASL _) = Experimental
      data_logic (GenCspCASL _) = Just (Logic CASL)
      empty_proof_tree _ = ()
      provers (GenCspCASL _) = cspProvers (undefined :: a)

-- | Static Analysis for CspCASL
instance Show a => StaticAnalysis (GenCspCASL a)
    -- basic_spec
    AS_CspCASL.CspBasicSpec
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
      stat_symb_items (GenCspCASL _) _ = cspStatSymbItems
      stat_symb_map_items (GenCspCASL _) _ = cspStatSymbMapItems
      symbol_to_raw (GenCspCASL _) = ACspSymbol
      empty_signature (GenCspCASL _) = SignCSP.emptyCspCASLSign
      is_subsig (GenCspCASL _) = SignCSP.isCspCASLSubSig
      subsig_inclusion (GenCspCASL _) = cspSubsigInclusion
      signature_union (GenCspCASL _) = SignCSP.unionCspCASLSign
      morphism_union (GenCspCASL _) =
          morphismUnion CspCASL_Morphism.cspAddMorphismUnion
                        SignCSP.cspSignUnion
