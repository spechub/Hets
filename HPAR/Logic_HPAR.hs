{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./HPAR/Logic_HPAR.hs
Description :  Instance of class Logic for HPAR


Instance of class Logic for rigid logic.
-}

module HPAR.Logic_HPAR where

import Logic.Logic
import HPAR.AS_Basic_HPAR
import HPAR.Sign
import HPAR.Morphism
import HPAR.ATC_HPAR ()
import HPAR.Parse_AS
import HPAR.Print_AS
import HPAR.StaticAna


import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Parse_AS_Basic as CParse
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor
--import CASL.MapSentence
--import CASL.SimplifySen
--import CASL.SymbolParser
--import CASL.Taxonomy
--import CASL.ToDoc
import CASL.Logic_CASL ()
import Common.Keywords (rigidS)

import Debug.Trace

data HPAR = HPAR deriving Show

instance Language HPAR where
 description _ = "HPAR\n" ++
                 "hybrid rigid partial algebras"

instance Category HSign HMorphism where
    ide = idMor
    inverse = undefined
    composeMorphisms = undefined
    dom = source
    cod = target
    isInclusion = undefined
    legal_mor = undefined

instance Syntax HPAR H_BASIC_SPEC CSign.Symbol H_SYMB_ITEMS CBasic.SYMB_MAP_ITEMS where
    parsersAndPrinters HPAR = 
           addSyntax "Hets" (basicSpec, pretty)
           $ makeDefault (basicSpec, pretty)
    parse_basic_spec HPAR = Just $ basicSpec
    parse_symb_items HPAR = undefined -- Just $ symbItems [rigidS]
    parse_symb_map_items HPAR = undefined -- Just $ symbMapItems hybrid_reserved_words

instance Sentences HPAR HFORMULA HSign HMorphism CSign.Symbol where
      map_sen HPAR = undefined -- return . mapSen map_H_FORMULA h
      sym_of HPAR = undefined -- symOf
      symmap_of HPAR = undefined --morphismToSymbMap
      sym_name HPAR = undefined --symName
      --simplify_sen HPAR = undefined --simplifyCASLSen
      --print_sign HPAR = pretty
      --print_named HPAR = undefined --printTheoryFormula

instance StaticAnalysis HPAR H_BASIC_SPEC HFORMULA
        H_SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
        HSign
        HMorphism
        CSign.Symbol CMor.RawSymbol where
                basic_analysis HPAR = Just $ basicAnalysis
                stat_symb_map_items HPAR = undefined --statSymbMapItems
                stat_symb_items HPAR = undefined --statSymbItems
                symbol_to_raw HPAR = undefined -- symbolToRaw
                id_to_raw HPAR = undefined --idToRaw
                matches HPAR = undefined --CASL.Morphism.matches
                empty_signature HPAR = emptySig
                signature_union HPAR s = undefined --return . addSig addRigidExt s
                intersection HPAR s = undefined --return . interSig interRigidExt s
                morphism_union HPAR = undefined --plainMorphismUnion (addSig addRigidExt)
                final_union HPAR = undefined --finalUnion (addSig addRigidExt)
                is_subsig HPAR = isSubSigOf
                subsig_inclusion HPAR = undefined -- sigInclusion emptyMorExt
                cogenerated_sign HPAR = undefined --cogeneratedSign emptyMorExt
                generated_sign HPAR = undefined -- generatedSign emptyMorExt
                induced_from_morphism HPAR = undefined -- inducedFromMorphism emptyMorExt
                induced_from_to_morphism HPAR = undefined --inducedFromToMorphism
                 -- emptyMorExt isSubRigidExt diffRigidExt
                theory_to_taxonomy HPAR = undefined --convTaxo

instance Logic HPAR ()
        H_BASIC_SPEC HFORMULA H_SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
        HSign
        HMorphism
        CSign.Symbol CMor.RawSymbol () where
                stability _ = Experimental
                empty_proof_tree _ = ()
                sem_constr _ = [SameInterpretation "rigid sort", SameInterpretation "rigid op", SameDomain True]

