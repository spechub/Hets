{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/ExtModal2CASL.hs
Copyright   :  (c) Christian Maeder, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (MPTC-FD)
-}

module Comorphisms.ExtModal2CASL (ExtModal2CASL (..)) where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.DocUtils
import Common.Id
import Common.ProofTree
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.HashSet as Set
import Data.Function
import Data.Maybe

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
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic ExtModal2CASL = ExtModal
    sourceSublogic ExtModal2CASL = mkTop foleml
    targetLogic ExtModal2CASL = CASL
    mapSublogic ExtModal2CASL s = Just s { ext_features = () }
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
    noNomsPreds = Set.foldr (`MapSet.delete` nomPType) rigPreds' noms
    termMs = termMods extInf
    rels = Set.foldr (\ m ->
      insertModPred world False (Set.member m termMs) m)
      MapSet.empty $ modalities extInf
    nomOps = Set.foldr (\ n -> addOpTo (nomName n) nomOpType) rigOps' noms
    in s1
    { sortRel = Rel.insertKey world $ sortRel sign
    , opMap = addOpMapSet flexOps' nomOps
    , assocOps = diffOpMapSet (assocOps sign) flexibleOps
    , predMap = addMapSet rels $ addMapSet flexPreds' noNomsPreds
    }

data Args = Args
  { currentW :: TERM ()
  , nextW, freeC :: Int  -- world variables
  , boundNoms :: [(Id, TERM ())]
  , modSig :: ExtModalSign
  }

transTop :: ExtModalSign -> CASLSign -> FORMULA EM_FORMULA -> FORMULA ()
transTop msig csig = let
    vd = mkVarDecl (genNumVar "w" 1) world
    vt = toQualVar vd
    in stripQuant csig . mkForall [vd]
           . transMF (Args vt 1 1 [] msig)

getTermOfNom :: Args -> Id -> TERM ()
getTermOfNom as i = fromMaybe (mkNomAppl i) . lookup i $ boundNoms as

mkNomAppl :: Id -> TERM ()
mkNomAppl pn = mkAppl (mkQualOp (nomName pn) $ toOP_TYPE nomOpType) []

transRecord :: Args -> Record EM_FORMULA (FORMULA ()) (TERM ())
transRecord as = let
    extInf = extendedInfo $ modSig as
    currW = currentW as
    in (mapRecord $ const ())
  { foldPredication = \ _ ps args r -> case ps of
      Qual_pred_name pn pTy@(Pred_type srts q) p
        | MapSet.member pn (toPredType pTy) $ flexPreds extInf
          -> Predication
            (Qual_pred_name (addPlace pn) (Pred_type (world : srts) q) p)
            (currW : args) r
        | null srts && Set.member pn (nominals extInf)
          -> mkStEq currW $ getTermOfNom as pn
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
  PrefixForm pf f r -> let
    fW = freeC as
    in case pf of
    BoxOrDiamond bOp m gEq i -> let
      ex = bOp == Diamond
      l = [fW + 1 .. fW + i]
      vds = map (\ n -> mkVarDecl (genNumVar "w" n) world) l
      nAs = as { freeC = fW + i }
      tf n = transMF nAs { currentW = mkVarTerm (genNumVar "w" n) world } f
      tM n = transMod nAs { nextW = n } m
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
    Hybrid at i -> let ni = simpleIdToId i in
      if at then transMF as { currentW = getTermOfNom as ni } f else let
      vi = mkVarDecl (genNumVar "i" $ fW + 1) world
      ti = toQualVar vi
      in mkExist [vi] $ conjunct
           [ mkStEq ti $ currentW as
           , transMF as { boundNoms = (ni, ti) : boundNoms as
                        , currentW = ti
                        , freeC = fW + 1 } f ]
    _ -> transMF as f
  UntilSince _isUntil f1 f2 r -> conjunctRange [transMF as f1, transMF as f2] r
  ModForm _ -> trueForm

transMod :: Args -> MODALITY -> FORMULA ()
transMod as md = let
  t1 = currentW as
  t2 = mkVarTerm (genNumVar "w" $ nextW as) world
  vts = [t1, t2]
  msig = modSig as
  extInf = extendedInfo msig
  in case md of
  SimpleMod i -> let ri = simpleIdToId i in mkPredication
    (mkQualPred (relOfMod False False ri)
                    . toPRED_TYPE $ modPredType world False ri) vts
  TermMod t -> case optTermSort t of
    Just srt -> case keepMinimals msig id . Set.toList
      . Set.intersection (termMods extInf) . Set.insert srt
      $ supersortsOf srt msig of
      [] -> error $ "transMod1: " ++ showDoc t ""
      st : _ -> mkPredication
        (mkQualPred (relOfMod False True st)
         . toPRED_TYPE $ modPredType world True st)
        $ foldTerm (transRecord as) t : vts
    _ -> error $ "transMod2: " ++ showDoc t ""
  Guard f -> conjunct [mkExEq t1 t2, transMF as f]
  ModOp mOp m1 m2 -> case mOp of
    Composition -> let
      nW = freeC as + 1
      nAs = as { freeC = nW }
      vd = mkVarDecl (genNumVar "w" nW) world
      in mkExist [vd] $ conjunct
           [ transMod nAs { nextW = nW } m1
           , transMod nAs { currentW = toQualVar vd } m2 ]
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
