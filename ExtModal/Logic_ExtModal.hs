{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for ExtModal
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher
Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  non-portable (imports Logic)

Instance of class Logic for ExtModal
-}

module ExtModal.Logic_ExtModal where

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.ATC_ExtModal()
import ExtModal.Parse_AS
import ExtModal.Print_AS
import ExtModal.StatAna
import ExtModal.MorphismExtension

import CASL.Formula
import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import CASL.SimplifySen
import CASL.Taxonomy
import CASL.Logic_CASL ()
import Logic.Logic

import qualified Data.Map as Map

data ExtModal = ExtModal deriving Show

instance Language ExtModal where
        description _ = unlines
         [ "ExtModal is the 'extended modal logic' extension of CASL. "
         , "Syntax for ordinary modalities, multi-modal logic, dynamic "
         , "logic, graded modal logic, hybrid logic, CTL* and mu-calculus  "
         , "is provided. Specific modal logics can be optained via "
         , "restrictions to sublanguages."
         ]

type ExtModalSign = Sign EM_FORMULA EModalSign
type ExtModalMorph = Morphism EM_FORMULA EModalSign MorphExtension
type ExtModalFORMULA = FORMULA EM_FORMULA

instance SignExtension EModalSign where
        isSubSignExtension = isSubEModalSign

instance Syntax ExtModal EM_BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
        parse_basic_spec ExtModal = Just $ basicSpec ext_modal_reserved_words
        parse_symb_items ExtModal = Just $ symbItems ext_modal_reserved_words
        parse_symb_map_items ExtModal =
            Just $ symbMapItems ext_modal_reserved_words

-- Modal formula mapping via signature morphism
map_EM_FORMULA :: MapSen EM_FORMULA EModalSign MorphExtension
map_EM_FORMULA morph (BoxOrDiamond choice t_m leq_geq number f pos) =
  let new_tm tm = case tm of
        Simple_modality sm ->
            let mds = mod_map (extended_map morph) in
            if Map.member sm mds then Simple_modality (mds Map.! sm) else tm
        Composition tm1 tm2 -> Composition (new_tm tm1) (new_tm tm2)
        Union tm1 tm2 -> Union (new_tm tm1) (new_tm tm2)
        TransitiveClosure tm1 -> TransitiveClosure (new_tm tm1)
        Guard frm -> Guard (mapSen map_EM_FORMULA morph frm)
      new_f = mapSen map_EM_FORMULA morph f
  in BoxOrDiamond choice (new_tm t_m) leq_geq number new_f pos


map_EM_FORMULA morph (Hybrid choice nm f pos) =
  let new_nom = case nm of
        Nominal nom -> let nms = nom_map (extended_map morph) in
          if Map.member nom nms then Nominal (nms Map.! nom) else nm
      new_f = mapSen map_EM_FORMULA morph f
  in Hybrid choice new_nom new_f pos


map_EM_FORMULA morph (UntilSince choice f1 f2 pos) =
        let new_f1 = mapSen map_EM_FORMULA morph f1
            new_f2 = mapSen map_EM_FORMULA morph f2
        in UntilSince choice new_f1 new_f2 pos

map_EM_FORMULA morph (NextY choice f pos) =
        let new_f = mapSen map_EM_FORMULA morph f
        in NextY choice new_f pos

map_EM_FORMULA morph (PathQuantification choice f pos) =
        let new_f = mapSen map_EM_FORMULA morph f
        in PathQuantification choice new_f pos

map_EM_FORMULA morph (StateQuantification t_dir choice f pos) =
        let new_f = mapSen map_EM_FORMULA morph f
        in StateQuantification t_dir choice new_f pos

map_EM_FORMULA morph (FixedPoint choice p_var f pos) =
        let new_f = mapSen map_EM_FORMULA morph f
        in FixedPoint choice p_var new_f pos

-- Simplification of formulas - simplifySen for ExtFORMULA
simEMSen :: Sign EM_FORMULA EModalSign -> EM_FORMULA -> EM_FORMULA
simEMSen sign (BoxOrDiamond choice tm leq_geq number f pos) =
        BoxOrDiamond choice tm leq_geq number
            (simplifySen frmTypeAna simEMSen sign f) pos
simEMSen sign (Hybrid choice nom f pos) =
        Hybrid choice nom (simplifySen frmTypeAna simEMSen sign f) pos
simEMSen sign (UntilSince choice f1 f2 pos) =
        UntilSince choice (simplifySen frmTypeAna simEMSen sign f1)
                (simplifySen frmTypeAna simEMSen sign f2) pos
simEMSen sign (NextY choice f pos) =
        NextY choice (simplifySen frmTypeAna simEMSen sign f) pos
simEMSen sign (PathQuantification choice f pos) =
        PathQuantification choice (simplifySen frmTypeAna simEMSen sign f) pos
simEMSen sign (StateQuantification t_dir choice f pos) =
        StateQuantification t_dir choice
            (simplifySen frmTypeAna simEMSen sign f) pos
simEMSen sign (FixedPoint choice p_var f pos) =
        FixedPoint choice p_var (simplifySen frmTypeAna simEMSen sign f) pos

instance Sentences ExtModal ExtModalFORMULA ExtModalSign ExtModalMorph Symbol
    where
        map_sen ExtModal morph = return . mapSen map_EM_FORMULA morph
        simplify_sen ExtModal = simplifySen frmTypeAna simEMSen
        parse_sentence ExtModal = Just $ primFormula ext_modal_reserved_words
        print_sign ExtModal sig = printSign
                (printEModalSign $ simplifySen frmTypeAna simEMSen sig) sig
        sym_of ExtModal = symOf
        symmap_of ExtModal = morphismToSymbMap
        sym_name ExtModal = symName

instance StaticAnalysis ExtModal EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
    SYMB_MAP_ITEMS ExtModalSign ExtModalMorph Symbol RawSymbol where
        basic_analysis ExtModal = Just basicEModalAnalysis
        stat_symb_map_items ExtModal = statSymbMapItems
        stat_symb_items ExtModal = statSymbItems

        symbol_to_raw ExtModal = symbolToRaw
        id_to_raw ExtModal = idToRaw
        matches ExtModal = CASL.Morphism.matches

        empty_signature ExtModal = emptySign emptyEModalSign
        signature_union ExtModal sgn = return . addSig addEModalSign sgn
        intersection ExtModal sgn = return . interSig interEModalSign sgn
        final_union ExtModal = finalUnion addEModalSign
        morphism_union ExtModal = morphismUnion (const id) addEModalSign
        is_subsig ExtModal = isSubSig isSubEModalSign
        subsig_inclusion ExtModal = sigInclusion emptyMorphExtension
        generated_sign ExtModal = generatedSign emptyMorphExtension
        cogenerated_sign ExtModal = cogeneratedSign emptyMorphExtension
        induced_from_morphism ExtModal = inducedFromMorphism emptyMorphExtension
        induced_from_to_morphism ExtModal =
          inducedFromToMorphism emptyMorphExtension isSubEModalSign
            diffEModalSign
        theory_to_taxonomy ExtModal = convTaxo

instance Logic ExtModal () EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
    SYMB_MAP_ITEMS ExtModalSign ExtModalMorph Symbol RawSymbol () where
        stability _ = Experimental
        empty_proof_tree _ = ()
