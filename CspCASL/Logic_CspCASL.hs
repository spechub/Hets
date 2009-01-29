{- |
Module      :  $Id$
Description :  CspCASL instance of type class logic
Copyright   :  (c)  Markus Roggenbach, Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  experimental
Portability :  non-portable(import Logic.Logic)

Here is the place where the class Logic is instantiated for CspCASL.
   Also the instances for Syntax an Category.
-}
{-
   todo:
     - writing real functions
     - Modul Sign.hs mit CSP-CASL-Signaturen und Morphismen, basiernd
       auf CASL.Sign
          CSP-CASL-Signatur = (CASL-Sig,Menge von Kanalnamen)
          CSP-CASL-Morphismus = (CASL-Morphismus, Kanalnamenabbildung)
                      oder nur CASL-Morphismus
          SYMB_ITEMS SYMB_MAP_ITEMS: erstmal von CASL (d.h. nur CASL-Morphismus)
     - instance Sentences
        Sätze = entweder CASL-Sätze oder CSP-CASL-Sätze
        Rest soweit wie möglich von CASL übernehmen
     - statische Analyse (gemäß Typ in Logic.Logic) schreiben
       und unten für basic_analysis einhängen

    Kür:
     - Teillogiken (instance SemiLatticeWithTop ...)

-}

module CspCASL.Logic_CspCASL
  ( GenCspCASL(..)
  , CspCASLSemantics
  , CspCASL
  , cspCASL
  , Trace(..)
  , traceCspCASL
  , Failure(..)
  , failureCspCASL
  ) where

import Logic.Logic
import Logic.Prover

import CASL.AS_Basic_CASL
import CASL.Logic_CASL
import CASL.Morphism
import CASL.Sign
import CASL.SymbolParser
import CASL.SymbolMapAnalysis

import qualified CspCASL.AS_CspCASL as AS_CspCASL
import qualified CspCASL.ATC_CspCASL()
import CspCASL.CspCASL_Keywords
import qualified CspCASL.Morphism as CspCASL_Morphism
import qualified CspCASL.Parse_CspCASL as Parse_CspCASL
import qualified CspCASL.Print_CspCASL ()
import qualified CspCASL.SignCSP as SignCSP
import qualified CspCASL.SimplifySen as SimplifySen
import qualified CspCASL.StatAnaCSP as StatAnaCSP

import CspCASLProver.CspCASLProver(cspCASLProver)

-- | a generic logic id for CspCASL with different semantics
data GenCspCASL a = GenCspCASL a deriving Show

cspCASL :: GenCspCASL ()
cspCASL = GenCspCASL ()

-- the top-level logic with the loosest semantics (and without provers)
type CspCASL = GenCspCASL ()

instance Show a => Language (GenCspCASL a) where
      language_name (GenCspCASL a) = "CspCASL"
        ++ let s = show a in if s == "()" then "" else '_' : s
      description _ =
        "CspCASL - see\n\n"++
        "http://www.cs.swan.ac.uk/~csmarkus/ProcessesAndData/"

instance SignExtension SignCSP.CspSign where
  isSubSignExtension = SignCSP.isInclusion

-- | Instance for CspCASL morphism extension (used for Category)
instance MorphismExtension SignCSP.CspSign SignCSP.CspAddMorphism where
  ideMorphismExtension _ = SignCSP.emptyCspAddMorphism
  composeMorphismExtension = SignCSP.composeCspAddMorphism
  inverseMorphismExtension = SignCSP.inverseCspAddMorphism
  isInclusionMorphismExtension _ = True -- missing!

-- | Instance of Sentences for CspCASL (missing)
instance Show a => Sentences (GenCspCASL a)
    SignCSP.CspCASLSen   -- sentence (missing)
    SignCSP.CspCASLSign     -- signature
    SignCSP.CspMorphism     -- morphism
    Symbol               -- symbol
    where
      map_sen (GenCspCASL _) mor sen =
        if isInclusionMorphism isInclusionMorphismExtension mor
        then return sen
        else fail "renaming in map_sen CspCASL not implemented"
      parse_sentence (GenCspCASL _) = Nothing
      sym_of (GenCspCASL _) = CspCASL_Morphism.symOf
      symmap_of (GenCspCASL _) = morphismToSymbMap
      sym_name (GenCspCASL _) = symName
      simplify_sen (GenCspCASL _) = SimplifySen.simplifySen

-- | Syntax of CspCASL
instance Show a => Syntax (GenCspCASL a)
    AS_CspCASL.CspBasicSpec -- basic_spec
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symb_map_items
    where
      parse_basic_spec (GenCspCASL _) =
          Just Parse_CspCASL.cspBasicSpec
      parse_symb_items (GenCspCASL _) =
          Just $ symbItemsExt [channelS, processS] csp_casl_keywords
      parse_symb_map_items (GenCspCASL _) =
          Just $ symbMapItemsExt [channelS, processS] csp_casl_keywords

-- lattices (for sublogics) missing


class Show a => CspCASLSemantics a where
  cspProvers :: a
    -> [Prover SignCSP.CspCASLSign SignCSP.CspCASLSen SignCSP.CspMorphism () ()]
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
    ()                      -- Sublogics (missing)
    AS_CspCASL.CspBasicSpec -- basic_spec
    SignCSP.CspCASLSen      -- sentence (missing)
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symb_map_items
    SignCSP.CspCASLSign     -- signature
    SignCSP.CspMorphism     -- morphism
    Symbol
    RawSymbol
    ()                      -- proof_tree (missing)
    where
      stability (GenCspCASL _) = Experimental
      data_logic (GenCspCASL _) = Just (Logic CASL)
      empty_proof_tree _ = ()
      provers (GenCspCASL _) = cspProvers (undefined :: a)

-- | Static Analysis for CspCASL
instance Show a => StaticAnalysis (GenCspCASL a)
    AS_CspCASL.CspBasicSpec -- basic_spec
    SignCSP.CspCASLSen      -- sentence (missing)
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symb_map_items
    SignCSP.CspCASLSign     -- signature
    SignCSP.CspMorphism     -- morphism
    Symbol
    RawSymbol
    where
      basic_analysis (GenCspCASL _) = Just StatAnaCSP.basicAnalysisCspCASL
      stat_symb_map_items (GenCspCASL _) = statSymbMapItems
      stat_symb_items (GenCspCASL _) = statSymbItems
      matches (GenCspCASL _) = CASL.Morphism.matches
      empty_signature (GenCspCASL _) = SignCSP.emptyCspCASLSign
      inclusion (GenCspCASL _) = sigInclusion
          SignCSP.emptyCspAddMorphism
          SignCSP.isInclusion const -- this is still wrong
      signature_union (GenCspCASL _) s =
          return . addSig SignCSP.addCspProcSig s
      induced_from_morphism (GenCspCASL _) = inducedFromMorphism
          SignCSP.emptyCspAddMorphism
      induced_from_to_morphism (GenCspCASL _) = inducedFromToMorphism
          SignCSP.emptyCspAddMorphism SignCSP.isInclusion
          SignCSP.diffCspProcSig
