{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (MPTC-FD)
-}

module Comorphisms.ExtModal2HasCASL where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Comorphisms.CASL2HasCASL

import qualified Data.Set as Set

-- CASL
import CASL.AS_Basic_CASL as CASL
import CASL.Morphism as CASL
import CASL.Sign as CASL
import CASL.World

-- ExtModalCASL
import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Sublogic as EM

import HasCASL.Logic_HasCASL
import HasCASL.As as HC
import HasCASL.AsUtils
import HasCASL.Le as HC
import HasCASL.Sublogic as HC

data ExtModal2HasCASL = ExtModal2HasCASL deriving (Show)
instance Language ExtModal2HasCASL

instance Comorphism ExtModal2HasCASL
               ExtModal EM.Sublogic EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               CASL.Symbol CASL.RawSymbol ()
               HasCASL HC.Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env HC.Morphism HC.Symbol HC.RawSymbol () where
    sourceLogic ExtModal2HasCASL = ExtModal
    sourceSublogic ExtModal2HasCASL = maxSublogic
    targetLogic ExtModal2HasCASL = HasCASL
    mapSublogic ExtModal2HasCASL _ = Just HC.caslLogic { which_logic = HOL }
    map_theory ExtModal2HasCASL (sig, sens) = case transSig sig sens of
      mme -> return (mme, [])
    {-
    map_morphism ExtModal2HasCASL = return . mapMor
    map_sentence ExtModal2HasCASL sig = return . transSen sig
    map_symbol ExtModal2HasCASL _ = Set.singleton . mapSym
    -}
    has_model_expansion ExtModal2HasCASL = True
    is_weakly_amalgamable ExtModal2HasCASL = True

nomName :: Id -> Id
nomName t = Id [genToken "N"] [t] $ rangeOfId t

nomOpType :: OpType
nomOpType = mkTotOpType [] world

tauId :: Id
tauId = genName "Tau"

tauTy :: PredType
tauTy = PredType [world, world]

-- | mixfix names work for tuples and are lost after currying
trI :: Id -> Id
trI i = if isMixfix i then Id [genToken "C"] [i] $ rangeOfId i else i

trOpSyn :: OP_TYPE -> Type
trOpSyn (Op_type ok args res _) = let
  (partial, total) = case ok of
    CASL.Total -> (HC.Total, True)
    CASL.Partial -> (HC.Partial, False)
  resTy = toType res
  in if null args then if total then resTy else mkLazyType resTy
  else getFunType resTy partial $ map toType args

trOp :: OpType -> TypeScheme
trOp = simpleTypeScheme . trOpSyn . toOP_TYPE

trPrSyn :: PRED_TYPE -> Type
trPrSyn (Pred_type args ps) = let u = unitTypeWithRange ps in
   if null args then mkLazyType u else
   getFunType u HC.Partial $ map toType args

trPr :: PredType -> TypeScheme
trPr = simpleTypeScheme . trPrSyn . toPRED_TYPE

-- | add world arguments to flexible ops and preds; and add relations
transSig :: ExtModalSign -> [Named (FORMULA EM_FORMULA)] -> Env
transSig sign sens = let
    s1 = embedSign () sign
    extInf = extendedInfo sign
    flexibleOps = flexOps extInf
    flexiblePreds = flexPreds extInf
    flexOps' = addWorldOp world id flexibleOps
    flexPreds' = addWorldPred world id flexiblePreds
    rigOps' = diffOpMapSet (opMap sign) flexibleOps
    rigPreds' = diffMapSet (predMap sign) flexiblePreds
    noms = nominals extInf
    noNomsPreds = Set.fold (`MapSet.delete` nomPType) rigPreds' noms
    termMs = termMods extInf
    timeMs = timeMods extInf
    rels = Set.fold (\ m ->
      insertModPred world (Set.member m timeMs) (Set.member m termMs) m)
      MapSet.empty $ modalities extInf
    nomOps = Set.fold (\ n -> addOpTo (nomName n) nomOpType) rigOps' noms
    s2 = s1
      { sortRel = Rel.insertKey world $ sortRel sign
      , opMap = addOpMapSet flexOps' nomOps
      , predMap = (if Set.null timeMs then id else MapSet.insert tauId tauTy)
                  . addMapSet rels $ addMapSet flexPreds' noNomsPreds
      }
    in mapSigAux trI trOp trPr (getConstructors sens) s2
