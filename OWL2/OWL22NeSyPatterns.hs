{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Inclusion comorphism from OWL 2 to NeSyPatterns
Copyright   :  (c) Till Mossakowksi
License     :  GPLv2 or higher, see LICENSE.txt

Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.OWL22NeSyPatterns (OWL22NeSyPatterns (..)) where

import Common.ProofTree
import ATC.ProofTree ()
import Logic.Logic as Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import qualified Data.Set as Set


-- OWL = domain
import OWL2.Logic_OWL2
import OWL2.AS as AS
import OWL2.ProfilesAndSublogics
import OWL2.ManchesterPrint ()
import OWL2.Morphism
import OWL2.Symbols
import qualified OWL2.Sign as OS
-- NeSyPatterns = codomain
import NeSyPatterns.Logic_NeSyPatterns
import NeSyPatterns.Sign
import NeSyPatterns.Morphism
import NeSyPatterns.AS
import NeSyPatterns.Symbol as Symbol
import NeSyPatterns.Analysis

data OWL22NeSyPatterns = OWL22NeSyPatterns deriving Show

instance Language OWL22NeSyPatterns

instance Comorphism
    OWL22NeSyPatterns        -- comorphism
    OWL2             -- lid domain
    ProfSub          -- sublogics domain
    OntologyDocument    -- Basic spec domain
    Axiom           -- sentence domain
    SymbItems       -- symbol items domain
    SymbMapItems    -- symbol map items domain
    OS.Sign         -- signature domain
    OWLMorphism     -- morphism domain
    Entity          -- symbol domain
    RawSymb         -- rawsymbol domain
    ProofTree       -- proof tree codomain
    NeSyPatterns            -- lid codomain
    ()  -- sublogics codomain
    BASIC_SPEC   -- Basic spec codomain
    ()    -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    Sign                          -- sign codomain
    Morphism                  -- morphism codomain
    Symbol                      -- symbol codomain
    Symbol                      -- raw_symbol codomain
    ProofTree                      -- proof_tree codomain
    where
      sourceLogic OWL22NeSyPatterns = OWL2
      sourceSublogic OWL22NeSyPatterns = topS
      targetLogic OWL22NeSyPatterns = NeSyPatterns
      mapSublogic OWL22NeSyPatterns _ = Just ()
      map_theory OWL22NeSyPatterns = mapTheory
      map_morphism OWL22NeSyPatterns = mapMorphism
      map_symbol OWL22NeSyPatterns _ = mapSymbol
      isInclusionComorphism OWL22NeSyPatterns = True
      isGTC OWL22NeSyPatterns = True

mapTheory :: (OS.Sign, [Named Axiom]) -> Result (Sign, [Named ()])
mapTheory (sig, sens) = return (emptySig{ owlClasses = OS.concepts sig
                                        , owlTaxonomy = subClassRelation $ map sentence sens}, [])

mapMorphism :: OWLMorphism -> Result Morphism
mapMorphism _ = fail "nyi"

mapSymbol :: Entity -> Set.Set Symbol
mapSymbol _ = Set.empty
