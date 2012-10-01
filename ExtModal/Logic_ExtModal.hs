{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for ExtModal
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  non-portable (imports Logic)

Instance of class Logic for ExtModal
-}

module ExtModal.Logic_ExtModal where

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.ATC_ExtModal ()
import ExtModal.Parse_AS
import ExtModal.StatAna
import ExtModal.MorphismExtension
import ExtModal.Sublogic

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.MapSentence
import CASL.Parse_AS_Basic
import CASL.SymbolParser
import CASL.SimplifySen
import CASL.Taxonomy
import CASL.ToDoc
import CASL.Logic_CASL ()

import Logic.Logic

import Common.DocUtils
import qualified Common.Lib.MapSet as MapSet
import qualified Data.Set as Set

data ExtModal = ExtModal deriving Show

instance Language ExtModal where
        description _ = unlines
         [ "ExtModal is the 'extended modal logic' extension of CASL. "
         , "Syntax for ordinary modalities, multi-modal logic, dynamic "
         , "logic, graded modal logic, hybrid logic, CTL* and mu-calculus  "
         , "is provided. Specific modal logics can be obtained via "
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

-- Simplification of formulas - simplifySen for ExtFORMULA
simEMSen :: Sign EM_FORMULA EModalSign -> EM_FORMULA -> EM_FORMULA
simEMSen sign = mapExtForm (simplifySen frmTypeAna simEMSen sign)

correctTarget :: Morphism f EModalSign m -> Morphism f EModalSign m
correctTarget m = m
  { mtarget = correctSign $ mtarget m
  , msource = correctSign $ msource m }

instance Sentences ExtModal ExtModalFORMULA ExtModalSign ExtModalMorph Symbol
    where
        map_sen ExtModal morph = return . mapSen mapEMform morph
        simplify_sen ExtModal = simplifySen frmTypeAna simEMSen
        print_named ExtModal = printTheoryFormula
        print_sign ExtModal sig = let e = extendedInfo sig in pretty sig
          { opMap = diffOpMapSet (opMap sig) $ flexOps e
          , predMap = Set.fold (`MapSet.delete` nomPType)
            (diffMapSet (predMap sig) $ flexPreds e) $ nominals e
          }
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
        signatureDiff ExtModal sgn = return . diffSig diffEModalSign sgn
        final_union ExtModal = finalUnion addEModalSign
        morphism_union ExtModal = plainMorphismUnion addEModalSign
        is_subsig ExtModal = isSubSig isSubEModalSign
        subsig_inclusion ExtModal = sigInclusion emptyMorphExtension
        generated_sign ExtModal s = fmap correctTarget
          . generatedSign emptyMorphExtension s
        cogenerated_sign ExtModal s = fmap correctTarget
          . cogeneratedSign emptyMorphExtension s
        induced_from_morphism ExtModal =
          inducedFromMorphismExt inducedEMsign
          (constMorphExt emptyMorphExtension)
        induced_from_to_morphism ExtModal =
          inducedFromToMorphismExt inducedEMsign
          (constMorphExt emptyMorphExtension)
          (\ _ _ -> return emptyMorphExtension) isSubEModalSign diffEModalSign
        theory_to_taxonomy ExtModal = convTaxo

instance Logic ExtModal Sublogic EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
    SYMB_MAP_ITEMS ExtModalSign ExtModalMorph Symbol RawSymbol () where
        stability _ = Experimental
        all_sublogics _ = sublogics_all
        empty_proof_tree _ = ()

instance SemiLatticeWithTop Sublogic where
    join = joinSublogic
    top = maxSublogic

instance MinSublogic Sublogic (FORMULA EM_FORMULA) where
    minSublogic = minSublogicOfForm

instance ProjectSublogic Sublogic EM_BASIC_SPEC where
    projectSublogic _ = id

instance MinSublogic Sublogic EM_BASIC_SPEC where
    minSublogic = minSublogicEMBasicSpec

instance ProjectSublogicM Sublogic SYMB_ITEMS where
    projectSublogicM _ = Just

instance MinSublogic Sublogic SYMB_ITEMS where
    minSublogic _ = botSublogic

instance ProjectSublogicM Sublogic SYMB_MAP_ITEMS where
    projectSublogicM _ = Just

instance MinSublogic Sublogic SYMB_MAP_ITEMS where
    minSublogic _ = botSublogic

instance ProjectSublogic Sublogic ExtModalSign where
    projectSublogic _ = id

instance MinSublogic Sublogic ExtModalSign where
    minSublogic = minSublogicExtModalSign

instance ProjectSublogic Sublogic ExtModalMorph where
    projectSublogic _ = id

instance MinSublogic Sublogic ExtModalMorph where
    minSublogic = minSublogicExtModalMorphism

instance ProjectSublogicM Sublogic Symbol where
    projectSublogicM _ = Just

instance MinSublogic Sublogic Symbol where
    minSublogic _ = botSublogic

instance SublogicName Sublogic where
    sublogicName = sublogic_name
