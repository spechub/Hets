{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (MPTC-FD)
-}

module Comorphisms.ExtModal2CASL where

import Logic.Logic
import Logic.Comorphism

import Common.ProofTree
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.World

-- ExtModalCASL
import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Sublogic

data ExtModal2CASL = ExtModal2CASL deriving (Show)
instance Language ExtModal2CASL

instance Comorphism ExtModal2CASL
               ExtModal Sublogic EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic ExtModal2CASL = ExtModal
    sourceSublogic ExtModal2CASL = maxSublogic
    targetLogic ExtModal2CASL = CASL
    mapSublogic ExtModal2CASL _ = Just SL.caslTop
    map_theory ExtModal2CASL (sig, _sens) = case transSig sig of
      mme -> return (mme, [])
    {-
    map_morphism ExtModal2CASL = return . mapMor
    map_sentence ExtModal2CASL sig = return . transSen sig
    map_symbol ExtModal2CASL _ = Set.singleton . mapSym
    -}
    has_model_expansion ExtModal2CASL = True
    is_weakly_amalgamable ExtModal2CASL = True

-- | add world arguments to flexible ops and preds; and add relations
transSig :: ExtModalSign -> CASLSign
transSig sign = let
    s1 = embedSign () sign
    extInf = extendedInfo sign
    flexibleOps = flexOps extInf
    flexiblePreds = flexPreds extInf
    flexOps' = addWorldOp world addPlace flexibleOps
    flexPreds' = addWorldPred world addPlace flexiblePreds
    rigOps' = diffOpMapSet (opMap sign) flexibleOps
    rigPreds' = diffMapSet (predMap sign) flexiblePreds
    termMs = termMods extInf
    timeMs = time_modalities extInf
    rels = Set.fold (\ m ->
      insertModPred world (Set.member m timeMs) (Set.member m termMs) m)
      MapSet.empty $ modalities extInf
    in s1
    { sortRel = Rel.insertKey world $ sortRel sign
    , opMap = addOpMapSet flexOps' rigOps'
    , assocOps = diffOpMapSet (assocOps sign) flexibleOps
    , predMap = addMapSet rels $ addMapSet flexPreds' rigPreds'}
