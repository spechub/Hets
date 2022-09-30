{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./RigidCASL/Logic_RigidCASL.hs
Description :  Instance of class Logic for rigid CASL
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable


Instance of class Logic for rigid logic.
-}

module RigidCASL.Logic_RigidCASL where

import Logic.Logic
import RigidCASL.AS_Rigid
import RigidCASL.Sign
import RigidCASL.Morphism
import RigidCASL.ATC_RigidCASL ()
import RigidCASL.Parse_AS ()
import RigidCASL.Print_AS
import RigidCASL.StaticAna

import CASL.Sign
import CASL.Formula(primFormula)
import CASL.StaticAna(convertCASLTheory, isNominalSen)
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.SimplifySen
import CASL.ToDoc
import CASL.Logic_CASL ()
import CASL.MapSentence
import CASL.SymbolMapAnalysis
import Common.Keywords (rigidS)

import CASL.SymbolParser

data RigidCASL = RigidCASL deriving Show

instance Language RigidCASL where
 description _ = "RigidCASL\n" ++
                 "Extends CASL with rigid symbols."

instance Syntax RigidCASL R_BASIC_SPEC RigidSymbol SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec RigidCASL = Just $ basicSpec [rigidS]
    parse_symb_items RigidCASL = Just . const $ symbItems [rigidS] -- this could be wrong!
    parse_symb_map_items RigidCASL = Just . const $ symbMapItems [rigidS]

-- Important convention: we use CASL syntax for quantifiers but variables are rigid! 
-- This must be taken into account when writing translations.

instance Sentences RigidCASL CASLFORMULA RSign RigidMor RigidSymbol where
      map_sen RigidCASL m = return . mapSen (const id) (caslMor m) -- return . mapSen map_H_FORMULA h
      sym_of RigidCASL = symOfRigid-- symOf -- this loses rigid symbols for now
      symmap_of RigidCASL = undefined --morphismToSymbMap
      sym_name RigidCASL = rigidSymName -- symName
      extSymKind RigidCASL = rigidExtSymKind
      simplify_sen RigidCASL = simplifyCASLSen
      print_sign RigidCASL sig = printSign printRigidExt $ removeRigidDupl sig
      print_named RigidCASL = printTheoryFormula
      is_nominal_sen RigidCASL = isNominalSen 

instance StaticAnalysis RigidCASL R_BASIC_SPEC CASLFORMULA
        SYMB_ITEMS SYMB_MAP_ITEMS
        RSign
        RigidMor
        RigidSymbol RawSymbol where
                basic_analysis RigidCASL = Just basicRigidAnalysis' -- was without '
                sen_analysis RigidCASL = Just rigidCASLsen_analysis
                convertTheory RigidCASL = Just convertCASLTheory
                add_noms_to_sign RigidCASL = addNomsToSign
                stat_symb_map_items RigidCASL = statSymbMapItems
                stat_symb_items RigidCASL = statSymbItems
                signature_colimit RigidCASL = sigColim
                signatureDiff RigidCASL s1 s2 = return $ diffSig diffRigidExt s1 s2
                symbol_to_raw RigidCASL = rigidSymToRaw -- symbolToRaw
                raw_to_symbol RigidCASL = rigidRawToSymbol
                raw_to_var RigidCASL = rawToVar
                id_to_raw RigidCASL = idToRaw
                matches RigidCASL = rigidMatches -- CASL.Morphism.matches
                empty_signature RigidCASL = emptySign emptyRigidExt
                add_symb_to_sign RigidCASL = rigidAddSymbToSign
                signature_union RigidCASL s = return . addSig addRigidExt s
                intersection RigidCASL s = return . interSig interRigidExt s
                morphism_union RigidCASL = undefined --plainMorphismUnion (addSig addRigidExt)
                final_union RigidCASL = undefined --finalUnion (addSig addRigidExt)
                is_subsig RigidCASL = isSubSig isSubRigidExt
                subsig_inclusion RigidCASL = sigInclusion emptyMorExt
                cogenerated_sign RigidCASL = undefined --cogeneratedSign emptyMorExt
                generated_sign RigidCASL = undefined -- generatedSign emptyMorExt
                induced_from_morphism RigidCASL = inducedFromMorphism emptyMorExt
                induced_from_to_morphism RigidCASL = undefined --inducedFromToMorphism
                 -- emptyMorExt isSubRigidExt diffRigidExt
                theory_to_taxonomy RigidCASL = undefined --convTaxo
                -- TODO: signature difference is missing!

instance Logic RigidCASL ()
        R_BASIC_SPEC CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        RSign
        RigidMor
        RigidSymbol RawSymbol () where
         stability _ = Experimental
         empty_proof_tree _ = ()
         -- helpers for hybridization
         constr_to_sens RigidCASL = rigidConstrToSens
         parse_prim_formula RigidCASL = Just (primFormula [])
           -- for each type, its name and the file where it is defined
         sublogicsTypeName RigidCASL = ("","")
         basicSpecTypeName RigidCASL = ("R_BASIC_SPEC","RigidCASL.AS_Rigid")
         sentenceTypeName RigidCASL = ("CASLFORMULA","CASL.AS_Basic_CASL")
         symbItemsTypeName RigidCASL = ("SYMB_ITEMS","CASL.AS_Basic_CASL")
         symbMapItemsTypeName RigidCASL = ("SYMB_MAP_ITEMS","CASL.AS_Basic_CASL")
         signTypeName RigidCASL = ("RSign","RigidCASL.Sign")
         morphismTypeName RigidCASL = ("RigidMor","RigidCASL.Morphism")
         symbolTypeName RigidCASL = ("RigidSymbol","RigidCASL.AS_Rigid")
         rawSymbolTypeName RigidCASL = ("RawSymbol","CASL.Morphism")
         proofTreeTypeName RigidCASL = ("","") 
