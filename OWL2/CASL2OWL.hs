{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CASL to OWL2
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.CASL2OWL where

import Logic.Logic as Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import qualified Data.Set as Set
import Common.Id
{-
import Control.Monad
import Data.Char
import qualified Data.Map as Map
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

-- the DL with the initial signature for OWL
import CASL_DL.PredefinedCASLAxioms
-}

-- OWL = codomain
import OWL2.Logic_OWL2
{-
import OWL2.Keywords
import OWL2.Parse
import OWL2.Print
-}
import OWL2.MS
import OWL2.AS
import OWL2.ProfilesAndSublogics
import OWL2.ManchesterPrint ()
import OWL2.Morphism
import OWL2.Symbols
import OWL2.Sign as OS
-- CASL = domain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic

import Common.ProofTree
{-
import Common.DocUtils

import Data.Maybe
import Text.ParserCombinators.Parsec
-}

data CASL2OWL = CASL2OWL deriving Show

instance Language CASL2OWL

instance Comorphism
    CASL2OWL        -- comorphism
    CASL            -- lid domain
    CASL_Sublogics  -- sublogics domain
    CASLBasicSpec   -- Basic spec domain
    CASLFORMULA     -- sentence domain
    SYMB_ITEMS      -- symbol items domain
    SYMB_MAP_ITEMS  -- symbol map items domain
    CASLSign        -- signature domain
    CASLMor         -- morphism domain
    Symbol          -- symbol domain
    RawSymbol       -- rawsymbol domain
    ProofTree       -- proof tree domain
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
      sourceLogic CASL2OWL = CASL
      sourceSublogic CASL2OWL = caslTop
      targetLogic CASL2OWL = OWL2
      mapSublogic CASL2OWL _ = Just topS
      map_theory CASL2OWL = mapTheory
      map_morphism CASL2OWL = mapMorphism
      map_symbol CASL2OWL _ = mapSymbol
      isInclusionComorphism CASL2OWL = True
      has_model_expansion CASL2OWL = True

-- | Mapping of CASL morphisms
mapMorphism :: CASLMor -> Result OWLMorphism
mapMorphism _ = fail "CASL2OWL.mapMorphism"

mapSymbol :: Symbol -> Set.Set Entity
mapSymbol _ = Set.empty

{- names must be disambiguated as is done in CASL.Qualify or SuleCFOL2SoftFOL.
   May ops or preds in the overload relation denote the same objectProperty?
-}
idToIRI :: Id -> QName
idToIRI i = nullQName
  { localPart = show i, iriPos = rangeOfId i }

mapSign :: CASLSign -> OS.Sign
mapSign csig = OS.emptySign
  { concepts = Set.map idToIRI $ sortSet csig }  -- map sorts to concepts

{- binary predicates and single argument functions should become
   objectProperties.
   Serge also turned constructors into concepts.
   How to treat multi-argument predicates and functions?
   Maybe create tuple concepts?
-}

mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (OS.Sign, [Named Axiom])
mapTheory (sig, _sens) = return (mapSign sig, [])
