{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Hybrid/Logic_Hybrid.hs
Description :  Instance of class Logic for Hybrid CASL


Instance of class Logic for hybrid logic.
-}

module Hybrid.Logic_Hybrid where

import Logic.Logic
import Hybrid.AS_Hybrid
import Hybrid.HybridSign
import Hybrid.ATC_Hybrid ()
import Hybrid.Parse_AS
import Hybrid.Print_AS
import Hybrid.StatAna
import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SimplifySen
import CASL.SymbolParser
import CASL.Taxonomy
import CASL.ToDoc
import CASL.Logic_CASL ()

import GHC.Generics (Generic)
import Data.Hashable

data Hybrid = Hybrid deriving (Show, Generic)

instance Hashable Hybrid

instance Language Hybrid where
 description _ = "Hybrid CASL\n" ++
                 "Extends an abitrary logic with at/modal operators."


type HSign = Sign H_FORMULA HybridSign
type HybridMor = Morphism H_FORMULA HybridSign (DefMorExt HybridSign)
type HybridFORMULA = FORMULA H_FORMULA

instance SignExtension HybridSign where
  isSubSignExtension = isSubHybridSign

instance Syntax Hybrid H_BASIC_SPEC Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec Hybrid = Just $ basicSpec hybrid_reserved_words
    parse_symb_items Hybrid = Just $ symbItems hybrid_reserved_words
    parse_symb_map_items Hybrid = Just $ symbMapItems hybrid_reserved_words

-- Hybrid logic
map_H_FORMULA :: MapSen H_FORMULA HybridSign (DefMorExt HybridSign)
map_H_FORMULA mor (BoxOrDiamond b m f ps) =
   let newM = case m of
                   Simple_mod _ -> m
                   Term_mod t -> let newT = mapTerm map_H_FORMULA mor t
                                 in Term_mod newT
       newF = mapSen map_H_FORMULA mor f
   in BoxOrDiamond b newM newF ps
map_H_FORMULA mor (At n f ps) = At n (mapSen map_H_FORMULA mor f) ps
map_H_FORMULA mor (Univ n f ps) = Univ n (mapSen map_H_FORMULA mor f) ps
map_H_FORMULA mor (Exist n f ps) = Exist n (mapSen map_H_FORMULA mor f) ps
map_H_FORMULA _ (Here n ps) = Here n ps

instance Sentences Hybrid HybridFORMULA HSign HybridMor Symbol where
      map_sen Hybrid h = return . mapSen map_H_FORMULA h
      sym_of Hybrid = symOf
      symmap_of Hybrid = morphismToSymbMap
      sym_name Hybrid = symName
      simplify_sen Hybrid = simplifySen minExpForm simHybrid
      print_sign Hybrid sig = printSign
          (printHybridSign $ simplifySen minExpForm simHybrid sig) sig
      print_named Hybrid = printTheoryFormula

-- simplifySen for ExtFORMULA
simHybrid :: Sign H_FORMULA HybridSign -> H_FORMULA -> H_FORMULA
simHybrid sign (BoxOrDiamond b md form pos) =
        let mod' = case md of
                Term_mod term -> Term_mod $ rmTypesT minExpForm
                                             simHybrid sign term
                t -> t
        in BoxOrDiamond b mod' (simplifySen minExpForm simHybrid sign form) pos
simHybrid sign (At n f ps) =
        At n (simplifySen minExpForm simHybrid sign f) ps
simHybrid sign (Univ n f ps) =
        Univ n (simplifySen minExpForm simHybrid sign f) ps
simHybrid sign (Exist n f ps) =
        Exist n (simplifySen minExpForm simHybrid sign f) ps

simHybrid _ (Here n ps) = Here n ps

rmTypesExt :: a -> b -> b
rmTypesExt _ f = f

instance StaticAnalysis Hybrid H_BASIC_SPEC HybridFORMULA
        SYMB_ITEMS SYMB_MAP_ITEMS
        HSign
        HybridMor
        Symbol RawSymbol where
                basic_analysis Hybrid = Just basicHybridAnalysis
                stat_symb_map_items Hybrid = statSymbMapItems
                stat_symb_items Hybrid = statSymbItems
                symbol_to_raw Hybrid = symbolToRaw
                id_to_raw Hybrid = idToRaw
                matches Hybrid = CASL.Morphism.matches
                empty_signature Hybrid = emptySign emptyHybridSign
                signature_union Hybrid s = return . addSig addHybridSign s
                intersection Hybrid s = return . interSig interHybridSign s
                morphism_union Hybrid = plainMorphismUnion addHybridSign
                final_union Hybrid = finalUnion addHybridSign
                is_subsig Hybrid = isSubSig isSubHybridSign
                subsig_inclusion Hybrid = sigInclusion emptyMorExt
                cogenerated_sign Hybrid = cogeneratedSign emptyMorExt
                generated_sign Hybrid = generatedSign emptyMorExt
                induced_from_morphism Hybrid = inducedFromMorphism emptyMorExt
                induced_from_to_morphism Hybrid = inducedFromToMorphism
                 emptyMorExt isSubHybridSign diffHybridSign
                theory_to_taxonomy Hybrid = convTaxo

instance Logic Hybrid ()
        H_BASIC_SPEC HybridFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        HSign
        HybridMor
        Symbol RawSymbol () where
                stability _ = Experimental
                empty_proof_tree _ = ()
