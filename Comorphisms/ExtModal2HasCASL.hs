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
import Common.DocUtils
import Common.Id
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Comorphisms.CASL2HasCASL

import CASL.AS_Basic_CASL as CASL
import CASL.Fold
import CASL.Morphism as CASL
import CASL.Overload
import CASL.Sign as CASL
import CASL.World

import Data.Maybe
import Data.Function
import qualified Data.Map as Map
import qualified Data.Set as Set

import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Sublogic as EM

import HasCASL.Logic_HasCASL
import HasCASL.As as HC
import HasCASL.AsUtils as HC
import HasCASL.Builtin
import HasCASL.Le as HC
import HasCASL.VarDecl
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
      mme -> return (mme, map (mapNamed $ toSen sig mme) sens)
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


data Args = Args
  { currentW :: Term
  , nextW, freeC :: Int  -- world variables
  , boundNoms :: [(Id, Term)]
  , modSig :: ExtModalSign
  }

varDecl :: Token -> SORT -> VarDecl
varDecl i s = VarDecl (simpleIdToId i) (toType s) Other nullRange

genVarDecl :: Token -> SORT -> GenVarDecl
genVarDecl i = GenVarDecl . varDecl i

varTerm :: Token -> SORT -> Term
varTerm i = QualVar . varDecl i

toSen :: ExtModalSign -> Env -> FORMULA EM_FORMULA -> Sentence
toSen msig env f = case f of
   Sort_gen_ax cs b -> let
       (sorts, ops, smap) = recover_Sort_gen_ax cs
       genKind = if b then Free else Generated
       mapPart :: OpKind -> Partiality
       mapPart cp = case cp of
                CASL.Total -> HC.Total
                CASL.Partial -> HC.Partial
       in DatatypeSen $ map ( \ s ->
          DataEntry (Map.fromList smap) s genKind [] rStar
          $ Set.fromList $ map ( \ (i, t) ->
            let args = map toType $ opArgs t in
            Construct (if isInjName i then Nothing else Just i) args
              (mapPart $ opKind t)
              $ map (\ a -> [Select Nothing a HC.Total]) args)
          $ filter ( \ (_, t) -> opRes t == s)
                $ map ( \ o -> case o of
                        Qual_op_name i t _ -> (trI i, toOpType t)
                        _ -> error "ExtModal2HasCASL.toSentence") ops) sorts
   _ -> Formula $ transTop msig env f

transTop :: ExtModalSign -> Env -> FORMULA EM_FORMULA -> Term
transTop msig env f = let
    vt = varTerm (genNumVar "w" 1) world
    in mkEnvForall env
           (transMF (Args vt 1 1 [] msig) f) nullRange

getTermOfNom :: Args -> Id -> Term
getTermOfNom as i = fromMaybe (mkNomAppl i) . lookup i $ boundNoms as

mkNomAppl :: Id -> Term
mkNomAppl pn = mkOpTerm (nomName pn) $ trOp nomOpType

trRecord :: Args -> String -> Record EM_FORMULA Term Term
trRecord as str = let
    extInf = extendedInfo $ modSig as
    currW = currentW as
    in (transRecord str)
  { foldPredication = \ _ ps args _ -> let
      Qual_pred_name pn pTy@(Pred_type srts q) p = ps
      in if MapSet.member pn (toPredType pTy) $ flexPreds extInf
         then mkApplTerm
            (mkOpTerm (trI pn) . simpleTypeScheme . trPrSyn
            $ Pred_type (world : srts) q) $ currW : args
         else if null srts && Set.member pn (nominals extInf)
              then mkEqTerm eqId (toType world) p currW $ getTermOfNom as pn
         else mkApplTerm
            (mkOpTerm (trI pn) . simpleTypeScheme $ trPrSyn pTy) args
  , foldExtFORMULA = \ _ f -> transEMF as f
  , foldApplication = \ _ os args _ -> let
      Qual_op_name opn oTy@(Op_type ok srts res q) _ = os
      in if MapSet.member opn (toOpType oTy) $ flexOps extInf
         then mkApplTerm
            (mkOpTerm (trI opn) . simpleTypeScheme . trOpSyn
            $ Op_type ok (world : srts) res q) $ currW : args
         else mkApplTerm
            (mkOpTerm (trI opn) . simpleTypeScheme $ trOpSyn oTy) args
  }

transMF :: Args -> FORMULA EM_FORMULA -> Term
transMF a f = foldFormula (trRecord a $ showDoc f "") f

disjointVars :: [VarDecl] -> [Term]
disjointVars vs = case vs of
  a : r@(b : _) -> mkTerm notId notType [] nullRange
    (on (mkEqTerm eqId (toType world) nullRange) QualVar a b) : disjointVars r
  _ -> []

transEMF :: Args -> EM_FORMULA -> Term
transEMF as emf = case emf of
  PrefixForm pf f r -> let
    fW = freeC as
    in case pf of
    BoxOrDiamond bOp m gEq i -> let
      ex = bOp == Diamond
      l = [fW + 1 .. fW + i]
      vds = map (\ n -> varDecl (genNumVar "w" n) world) l
      gvs = map GenVarDecl vds
      nAs = as { freeC = fW + i }
      tf n = transMF nAs { currentW = varTerm (genNumVar "w" n) world } f
      tM n = transMod nAs { nextW = n } m
      conjF = toBinJunctor andId
        (map tM l ++ map tf l ++ disjointVars vds) r
      diam = BoxOrDiamond Diamond m True
      tr b = transEMF as $ PrefixForm (BoxOrDiamond b m gEq i) f r
      f1 = QuantifiedTerm HC.Existential gvs conjF r
      f2 = HC.mkForall gvs conjF
      in if gEq && i > 0 && (i == 1 || ex) then case bOp of
           Diamond -> f1
           Box -> f2
           EBox -> toBinJunctor andId [f1, f2] r
         else if i <= 0 && ex && gEq then unitTerm trueId r
         else if bOp == EBox then toBinJunctor andId (map tr [Diamond, Box]) r
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
      vi = varDecl (genNumVar "i" $ fW + 1) world
      ti = QualVar vi
      in QuantifiedTerm HC.Existential [GenVarDecl vi]
           (toBinJunctor andId
           [ mkEqTerm eqId (toType world) r ti $ currentW as
           , transMF as { boundNoms = (ni, ti) : boundNoms as
                        , currentW = ti
                        , freeC = fW + 1 } f ] r) r
    _ -> transMF as f
  UntilSince _isUntil f1 f2 r ->
    toBinJunctor andId [transMF as f1, transMF as f2] r
  ModForm _ -> unitTerm trueId nullRange

transMod :: Args -> MODALITY -> Term
transMod as md = let
  t1 = currentW as
  t2 = varTerm (genNumVar "w" $ nextW as) world
  vts = [t1, t2]
  msig = modSig as
  extInf = extendedInfo msig
  timeMs = timeMods extInf
  in case md of
  SimpleMod i -> let ri = simpleIdToId i in mkApplTerm
    (mkOpTerm (relOfMod (Set.member ri timeMs) False ri)
                    . trPr $ modPredType world False ri) vts
  TermMod t -> case optTermSort t of
    Just srt -> case keepMinimals msig id . Set.toList
      . Set.intersection (termMods extInf) . Set.insert srt
      $ supersortsOf srt msig of
      [] -> error $ "transMod1: " ++ showDoc t ""
      st : _ -> mkApplTerm
        (mkOpTerm (relOfMod (Set.member st timeMs) True st)
         . trPr $ modPredType world True st)
        $ foldTerm (trRecord as $ showDoc t "") t : vts
    _ -> error $ "transMod2: " ++ showDoc t ""
  Guard f -> toBinJunctor andId
    [mkEqTerm exEq (toType world) nullRange t1 t2, transMF as f] nullRange
  ModOp mOp m1 m2 -> case mOp of
    Composition -> let
      nW = freeC as + 1
      nAs = as { freeC = nW }
      vd = varDecl (genNumVar "w" nW) world
      in QuantifiedTerm HC.Existential [GenVarDecl vd] (toBinJunctor andId
           [ transMod nAs { nextW = nW } m1
           , transMod nAs { currentW = QualVar vd } m2 ] nullRange)
         nullRange
    Intersection -> toBinJunctor andId [transMod as m1, transMod as m2]
       nullRange
    Union -> toBinJunctor orId [transMod as m1, transMod as m2] nullRange
    OrElse -> toBinJunctor orId (transOrElse [] as $ flatOrElse md) nullRange
  TransClos m -> transMod as m -- ignore transitivity for now

flatOrElse :: MODALITY -> [MODALITY]
flatOrElse md = case md of
  ModOp OrElse m1 m2 -> flatOrElse m1 ++ flatOrElse m2
  _ -> [md]

transOrElse :: [FORMULA EM_FORMULA] -> Args -> [MODALITY] -> [Term]
transOrElse nFs as ms = case ms of
  [] -> []
  md : r -> case md of
    Guard f -> transMod as (Guard . conjunct $ f : nFs)
      : transOrElse (mkNeg f : nFs) as r
    _ -> transMod as md : transOrElse nFs as r
