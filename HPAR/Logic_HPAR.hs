{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./HPAR/Logic_HPAR.hs
Description :  Instance of class Logic for HPAR
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable


Instance of class Logic for HPAR.
-}

module HPAR.Logic_HPAR where

import Logic.Logic
import Logic.SemConstr
import HPAR.AS_Basic_HPAR
import HPAR.Sign
import HPAR.Morphism
import HPAR.ATC_HPAR ()
import HPAR.Parse_AS
import HPAR.StaticAna

import qualified HPAR.Symbol as HSym
import qualified Data.Map as Map


import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sign as CSign ()
import qualified CASL.Morphism as CMor
import HPAR.SimplifySen
import CASL.Logic_CASL ()

import qualified RigidCASL.Logic_RigidCASL as RLogic

data HPAR = HPAR deriving Show

instance Language HPAR where
 description _ = "HPAR\n" ++
                 "hybrid rigid partial algebras"

instance Category HSign HMorphism where
    ide = idMor
    inverse = error "inverse nyi"
    composeMorphisms = error "compose morphisms nyi"
    dom = source
    cod = target
    isInclusion = isInclusionMor
    legal_mor = error "legal mor nyi"

instance Syntax HPAR H_BASIC_SPEC HSym.HSymbol H_SYMB_ITEMS CBasic.SYMB_MAP_ITEMS where
    -- parsersAndPrinters HPAR = makeDefault (basicSpec, pretty) TODO: default implementation is fine
    parse_basic_spec HPAR = Just $ basicSpec
    parse_symb_items HPAR = error "parse symb items nyi" -- Just $ symbItems [rigidS]
    parse_symb_map_items HPAR = error "parse symb map items nyi" -- Just $ symbMapItems hybrid_reserved_words

instance Sentences HPAR HFORMULA HSign HMorphism HSym.HSymbol where
      map_sen HPAR = error "map_sen nyi" -- return . mapSen map_H_FORMULA h
      sym_of HPAR = HSym.symOf -- TODO:this loses modalities and nominals!!!
      symmap_of HPAR hmor = Map.mapKeys (\x -> HSym.BSymbol x) $ Map.map (\x -> HSym.BSymbol x) $ CMor.morphismToSymbMap $ baseMor hmor -- TODO: this loses modalities and nominals
      sym_name HPAR = HSym.symName
      simplify_sen HPAR = simplifyHPARSen
      --print_sign HPAR = pretty
      --print_named HPAR = error "nyi" --printTheoryFormula

instance StaticAnalysis HPAR H_BASIC_SPEC HFORMULA
        H_SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
        HSign
        HMorphism
        HSym.HSymbol CMor.RawSymbol where
                basic_analysis HPAR = Just $ basicAnalysis
                stat_symb_map_items HPAR = error "sym_name nyi" --statSymbMapItems
                stat_symb_items HPAR = error "sym_name nyi" --statSymbItems
                symbol_to_raw HPAR = error "sym_name nyi" -- symbolToRaw
                id_to_raw HPAR = error "sym_name nyi"  --idToRaw
                matches HPAR = error "nyi" --CASL.Morphism.matches
                empty_signature HPAR = emptySig
                signature_union HPAR = error "sig union nyi" --return . addSig addRigidExt s
                intersection HPAR = error "nyi" --return . interSig interRigidExt s
                morphism_union HPAR = error "nyi" --plainMorphismUnion (addSig addRigidExt)
                final_union HPAR = error "nyi" --finalUnion (addSig addRigidExt)
                is_subsig HPAR = isSubSigOf
                subsig_inclusion HPAR s1 s2  = return $ inclusionMap s1 s2
                cogenerated_sign HPAR = error "nyi" --cogeneratedSign emptyMorExt
                generated_sign HPAR = error "nyi" -- generatedSign emptyMorExt
                induced_from_morphism HPAR = error "nyi" -- inducedFromMorphism emptyMorExt
                induced_from_to_morphism HPAR = error "nyi" --inducedFromToMorphism
                 -- emptyMorExt isSubRigidExt diffRigidExt
                theory_to_taxonomy HPAR = error "nyi" --convTaxo

instance Logic HPAR ()
        H_BASIC_SPEC HFORMULA H_SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
        HSign
        HMorphism
        HSym.HSymbol CMor.RawSymbol () where
                stability _ = Experimental
                empty_proof_tree _ = ()
                sem_constr _ = [ SameInterpretation "rigid sort"
                               , SameInterpretation "rigid op" 
                               , SameDomain True]
                data_logic _ = Just $ Logic RLogic.RigidCASL

