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
import Common.DocUtils
import Common.Id
import Common.ProofTree
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set
import Data.Function

-- CASL
import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Logic_CASL
import CASL.Morphism
import CASL.Overload
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
           . transMF (Args 1 1 (stringToId "Z") msig)

transRecord :: Args -> Record EM_FORMULA (FORMULA ()) (TERM ())
transRecord as = let
    extInf = extendedInfo $ modSig as
    currW = mkVarTerm (genNumVar "w" $ futureW as) world
    in (mapRecord $ const ())
  { foldPredication = \ _ ps args r -> case ps of
      Qual_pred_name pn pTy@(Pred_type srts q) p
        | MapSet.member pn (toPredType pTy) $ flexPreds extInf
          -> Predication
            (Qual_pred_name (addPlace pn) (Pred_type (world : srts) q) p)
            (currW : args) r
        | null srts && Set.member pn (nominals extInf)
          -> mkStEq currW $ mkAppl
             (mkQualOp (nomName pn) $ toOP_TYPE nomOpType) []
      _ -> Predication ps args r
  , foldExtFORMULA = \ _ f -> transEMF as f
  , foldApplication = \ _ os args r -> case os of
      Qual_op_name opn oTy@(Op_type ok srts res q) p
        | MapSet.member opn (toOpType oTy) $ flexOps extInf
          -> Application
            (Qual_op_name (addPlace opn) (Op_type ok (world : srts) res q) p)
            (currW : args) r
      _ -> Application os args r
  }

transMF :: Args -> FORMULA EM_FORMULA -> FORMULA ()
transMF = foldFormula . transRecord

disjointVars :: [VAR_DECL] -> [FORMULA ()]
disjointVars vs = case vs of
  a : r@(b : _) -> mkNeg (on mkStEq toQualVar a b) : disjointVars r
  _ -> []

transEMF :: Args -> EM_FORMULA -> FORMULA ()
transEMF as emf = case emf of
  PrefixForm pf f r -> case pf of
    BoxOrDiamond bOp m gEq i -> let
      fW = max (futureW as) $ currentW as
      ex = bOp == Diamond
      l = [fW + 1 .. fW + i]
      vds = map (\ n -> mkVarDecl (genNumVar "w" n) world) l
      nAs n = as { futureW = n }
      tf n = transMF (nAs n) f
      tM n = transMod (nAs n) m
      conjF = conjunct $ map tM l ++ map tf l ++ disjointVars vds
      diam = BoxOrDiamond Diamond m True
      tr b = transEMF as $ PrefixForm (BoxOrDiamond b m gEq i) f r
      in if gEq && i > 0 && (i == 1 || ex) then case bOp of
           Diamond -> mkExist vds conjF
           Box -> mkForall vds conjF
           EBox -> conjunct [mkExist vds conjF, mkForall vds conjF]
         else if i <= 0 && ex && gEq then trueForm
         else if bOp == EBox then conjunct $ map tr [Diamond, Box]
         else if ex -- lEq
              then transMF as . mkNeg . ExtFORMULA $ PrefixForm
                       (diam $ i + 1) f r
         else if gEq -- Box
              then transMF as . mkNeg . ExtFORMULA $ PrefixForm
                       (diam i) (mkNeg f) r
              else transMF as . ExtFORMULA $ PrefixForm
                       (diam $ i + 1) (mkNeg f) r
    _ -> transMF as f
  UntilSince _isUntil f1 f2 r -> conjunctRange [transMF as f1, transMF as f2] r
  ModForm _ -> trueForm

transMod :: Args -> MODALITY -> FORMULA ()
transMod as md = let
  fW = futureW as
  cW = currentW as
  vts@[t1, t2] = map (\ n -> mkVarTerm (genNumVar "w" n) world)
             [currentW as, fW]
  msig = modSig as
  extInf = extendedInfo msig
  timeMs = timeMods extInf
  in case md of
  SimpleMod i -> let ri = simpleIdToId i in mkPredication
    (mkQualPred (relOfMod (Set.member ri timeMs) False ri)
                    . toPRED_TYPE $ modPredType world False ri) vts
  TermMod t -> case optTermSort t of
    Just srt -> case keepMinimals msig id . Set.toList
      . Set.intersection (termMods extInf) . Set.insert srt
      $ supersortsOf srt msig of
      [] -> error $ "transMod1: " ++ showDoc t ""
      st : _ -> mkPredication
        (mkQualPred (relOfMod (Set.member st timeMs) True st)
         . toPRED_TYPE $ modPredType world True st)
        $ foldTerm (transRecord as) t : vts
    _ -> error $ "transMod2: " ++ showDoc t ""
  Guard f -> conjunct [mkExEq t1 t2,
      transMF as { futureW = cW } f]
  ModOp mOp m1 m2 -> case mOp of
    Composition -> let
      nW = max fW cW + 1
      vd = mkVarDecl (genNumVar "w" nW) world
      in mkExist [vd] $ conjunct
           [ transMod as { futureW = nW } m1
           , transMod as { currentW = nW } m2 ]
    Intersection -> conjunct [transMod as m1, transMod as m2] -- parallel?
    Union -> disjunct [transMod as m1, transMod as m2]
    OrElse -> disjunct . transOrElse [] as $ flatOrElse md
  TransClos m -> transMod as m -- ignore transitivity for now

flatOrElse :: MODALITY -> [MODALITY]
flatOrElse md = case md of
  ModOp OrElse m1 m2 -> flatOrElse m1 ++ flatOrElse m2
  _ -> [md]

transOrElse :: [FORMULA EM_FORMULA] -> Args -> [MODALITY] -> [FORMULA ()]
transOrElse nFs as ms = case ms of
  [] -> []
  md : r -> case md of
    Guard f -> transMod as (Guard . conjunct $ f : nFs)
      : transOrElse (mkNeg f : nFs) as r
    _ -> transMod as md : transOrElse nFs as r
