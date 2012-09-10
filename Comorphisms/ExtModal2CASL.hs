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

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

-- CASL
import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Logic_CASL
import CASL.Morphism
import CASL.Quantification
import CASL.Sign
import CASL.Sublogic as SL
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
    map_theory ExtModal2CASL (sig, sens) = case transSig sig of
      mme -> return (mme, map (mapNamed $ transTop sig mme) sens)
    {-
    map_morphism ExtModal2CASL = return . mapMor
    map_sentence ExtModal2CASL sig = return . transSen sig
    map_symbol ExtModal2CASL _ = Set.singleton . mapSym
    -}
    has_model_expansion ExtModal2CASL = True
    is_weakly_amalgamable ExtModal2CASL = True

nomName :: Id -> Id
nomName t = Id [genToken "N"] [t] $ rangeOfId t

nomOpType :: OpType
nomOpType = mkTotOpType [] world

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
    noms = nominals extInf
    noNomsPreds = Set.fold (`MapSet.delete` nomPType) rigPreds' noms
    termMs = termMods extInf
    timeMs = timeMods extInf
    rels = Set.fold (\ m ->
      insertModPred world (Set.member m timeMs) (Set.member m termMs) m)
      MapSet.empty $ modalities extInf
    nomOps = Set.fold (\ n -> addOpTo (nomName n) nomOpType) rigOps' noms
    in s1
    { sortRel = Rel.insertKey world $ sortRel sign
    , opMap = addOpMapSet flexOps' nomOps
    , assocOps = diffOpMapSet (assocOps sign) flexibleOps
    , predMap = addMapSet rels $ addMapSet flexPreds' noNomsPreds}

data Args = Args
  { currentW, futureW :: Int  -- world variables
  , currentN, futureN :: Int  -- world numbering
  , transPredName :: Id
  , modSig :: ExtModalSign
  }

natSort :: SORT
natSort = stringToId "Nat"

-- TODO: check that constructors are not flexible!

transTop :: ExtModalSign -> CASLSign -> FORMULA EM_FORMULA -> FORMULA ()
transTop msig csig = let
    vd = mkVarDecl (genNumVar "w" 1) world
    vn = mkVarDecl (genNumVar "n" 1) natSort
    in stripQuant csig . mkForall [vd, vn]
           . transMF (Args 1 1 1 1 (stringToId "Z") msig)

transMF :: Args -> FORMULA EM_FORMULA -> FORMULA ()
transMF as = let
    extInf = extendedInfo $ modSig as
    currW = mkVarTerm (genNumVar "w" $ futureW as) world
    in foldFormula (mapRecord $ const ())
  { foldPredication = \ _ ps args r -> case ps of
      Qual_pred_name pn pTy@(Pred_type srts q) p
        | MapSet.member pn (toPredType pTy) $ flexPreds extInf
          -> Predication
            (Qual_pred_name (addPlace pn) (Pred_type (world : srts) q) p)
            (currW : args) r
        | null srts && Set.member pn (nominals extInf)
          -> mkStEq (currW) $ mkAppl
             (mkQualOp (nomName pn) $ toOP_TYPE nomOpType) []
      _ -> Predication ps args r
  , foldExtFORMULA = \ _ f -> transEMF as f
  , foldApplication = \ _ os args r -> case os of
      Qual_op_name on oTy@(Op_type ok srts res q) p
        | MapSet.member on (toOpType oTy) $ flexOps extInf
          -> Application
            (Qual_op_name (addPlace on) (Op_type ok (world : srts) res q) p)
            (currW : args) r
      _ -> Application os args r
  }

transEMF :: Args -> EM_FORMULA -> FORMULA ()
transEMF as emf = case emf of
  PrefixForm pf f _ -> case pf of
    BoxOrDiamond _bOp _m _grad i -> let
      tf = transMF as { futureW = futureW as + i } f
      -- tM = transMod as m
      in tf
    _ -> transMF as f
  UntilSince _isUntil f1 f2 r -> conjunctRange [transMF as f1, transMF as f2] r
  ModForm _ -> trueForm
