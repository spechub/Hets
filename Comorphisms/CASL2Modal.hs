{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  embedding from CASL to ModalCASL
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to ModalCASL.

-}

module Comorphisms.CASL2Modal (CASL2Modal(..)) where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import Common.ProofTree

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- ModalCASL
import Modal.Logic_Modal
import Modal.AS_Modal
import Modal.ModalSign

-- | The identity of the comorphism
data CASL2Modal = CASL2Modal deriving (Show)

instance Language CASL2Modal -- default definition is okay

instance Comorphism CASL2Modal
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               Modal ()
               M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MSign
               ModalMor
               Symbol RawSymbol () where
    sourceLogic CASL2Modal = CASL
    sourceSublogic CASL2Modal = SL.top
    targetLogic CASL2Modal = Modal
    mapSublogic CASL2Modal _ = Just ()
    map_theory CASL2Modal = return . simpleTheoryMapping mapSig mapSen
    map_morphism CASL2Modal = return . mapMor
    map_sentence CASL2Modal _ = return . mapSen
    map_symbol CASL2Modal _ = Set.singleton . mapSym
    has_model_expansion CASL2Modal = True
    is_weakly_amalgamable CASL2Modal = True
    isInclusionComorphism CASL2Modal = True

mapSig :: CASLSign -> MSign
mapSig sign =
     (emptySign emptyModalSign) {sortSet = sortSet sign
               , sortRel = sortRel sign
               , opMap = opMap sign
               , assocOps = assocOps sign
               , predMap = predMap sign }

mapMor :: CASLMor -> ModalMor
mapMor m = (embedMorphism emptyMorExt (mapSig $ msource m) $ mapSig $ mtarget m)
  { sort_map = sort_map m
  , op_map = op_map m
  , pred_map = pred_map m }

mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once modal symbols are added


mapSen :: CASLFORMULA -> ModalFORMULA
mapSen f = case f of
    Quantification q vs frm ps ->
        Quantification q vs (mapSen frm) ps
    Conjunction fs ps ->
        Conjunction (map mapSen fs) ps
    Disjunction fs ps ->
        Disjunction (map mapSen fs) ps
    Implication f1 f2 b ps ->
        Implication (mapSen f1) (mapSen f2) b ps
    Equivalence f1 f2 ps ->
        Equivalence (mapSen f1) (mapSen f2) ps
    Negation frm ps -> Negation (mapSen frm) ps
    True_atom ps -> True_atom ps
    False_atom ps -> False_atom ps
    Existl_equation t1 t2 ps ->
        Existl_equation (mapTERM t1) (mapTERM t2) ps
    Strong_equation t1 t2 ps ->
        Strong_equation (mapTERM t1) (mapTERM t2) ps
    Predication pn as qs ->
        Predication pn (map mapTERM as) qs
    Definedness t ps -> Definedness (mapTERM t) ps
    Membership t ty ps -> Membership (mapTERM t) ty ps
    Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
    _ -> error "CASL2Modal.mapSen"

mapTERM :: TERM () -> TERM M_FORMULA
mapTERM t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs  -> Application opsym (map mapTERM as) qs
    Sorted_term trm ty ps -> Sorted_term (mapTERM trm) ty ps
    Cast trm ty ps -> Cast (mapTERM trm) ty ps
    Conditional t1 f t2 ps ->
       Conditional (mapTERM t1) (mapSen f) (mapTERM t2) ps
    _ -> error "CASL2Modal.mapTERM"
