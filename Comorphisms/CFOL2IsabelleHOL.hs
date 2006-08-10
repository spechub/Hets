{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to Isabelle-HOL.
-}

module Comorphisms.CFOL2IsabelleHOL
    ( CFOL2IsabelleHOL(..)
    , transTheory
    , mapSen
    , IsaTheory
    , SignTranslator
    , FormulaTranslator
    , quantifyIsa
    , transSort
    , transOP_SYMB
    , var
    ) where

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Morphism
import CASL.Quantification
import CASL.Overload

import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

import Common.AS_Annotation
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import qualified Data.List as List
import Data.Maybe (mapMaybe)

-- | The identity of the comorphism
data CFOL2IsabelleHOL = CFOL2IsabelleHOL deriving (Show)

-- Isabelle theories
type IsaTheory = (IsaSign.Sign, [Named IsaSign.Sentence])

-- extended signature translation
type SignTranslator f e = CASL.Sign.Sign f e -> e -> IsaTheory -> IsaTheory

-- extended signature translation for CASL
sigTrCASL :: SignTranslator () ()
sigTrCASL _ _ = id

-- extended formula translation
type FormulaTranslator f e = CASL.Sign.Sign f e -> f -> Term

-- extended formula translation for CASL
formTrCASL :: FormulaTranslator () ()
formTrCASL _ _ = error "CFOL2IsabelleHOL: No extended formulas allowed in CASL"

instance Language CFOL2IsabelleHOL -- default definition is okay

instance Comorphism CFOL2IsabelleHOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic _ = CASL
    sourceSublogic _ = SL.top
                      { sub_features = NoSub, -- no subsorting yet ...
                        has_part = False -- no partiality yet ...
                      }
    targetLogic _ = Isabelle
    mapSublogic _ _ = ()
    map_theory _ = transTheory sigTrCASL formTrCASL
    map_morphism = mapDefaultMorphism
    map_sentence _ sign =
      return . mapSen formTrCASL sign
    map_symbol = errMapSymbol

---------------------------- Signature -----------------------------
baseSign :: BaseSig
baseSign = Main_thy

transTheory :: SignTranslator f e ->
               FormulaTranslator f e ->
               (CASL.Sign.Sign f e, [Named (FORMULA f)])
                   -> Result IsaTheory
transTheory trSig trForm (sign, sens) =
  fmap (trSig sign (extendedInfo sign)) $
  return (IsaSign.emptySign {
    baseSig = baseSign,
    tsig = emptyTypeSig {arities =
               Set.fold (\s -> let s1 = showIsaTypeT s baseSign in
                                 Map.insert s1 [(isaTerm, [])])
                               Map.empty (sortSet sign)},
    constTab = Map.foldWithKey insertPreds
                (Map.foldWithKey insertOps Map.empty
                $ opMap sign) $ predMap sign,
    domainTab = dtDefs},
         map (mapNamed (mapSen trForm sign)) real_sens)
     -- for now, no new sentences
  where
    (real_sens, sort_gen_axs) = List.partition
        (\ s -> case sentence s of
                Sort_gen_ax _ _ -> False
                _ -> True) sens
    dtDefs = makeDtDefs sign sort_gen_axs
    ga = globAnnos sign
    insertOps op ts m = case Set.lookupSingleton ts of
      Just t ->
           Map.insert (mkIsaConstT False ga (length $ opArgs t) op baseSign)
               (transOpType t) m
      Nothing -> foldl (\m1 (t,i) ->
             Map.insert (mkIsaConstIT False ga
                         (length $ opArgs t) op i baseSign)
                    (transOpType t) m1) m
                (zip (Set.toList ts) [1..])
    insertPreds pre ts m = case Set.lookupSingleton ts of
      Just t ->
           Map.insert (mkIsaConstT True ga (length $ predArgs t) pre baseSign)
               (transPredType (Set.findMin ts)) m
      Nothing ->  foldl (\m1 (t,i) ->
             Map.insert (mkIsaConstIT True ga
                         (length $ predArgs t) pre i baseSign)
                    (transPredType t) m1) m
                (zip (Set.toList ts) [1..])

makeDtDefs :: CASL.Sign.Sign f e -> [Named (FORMULA f)]
               -> [[(Typ,[(VName,[Typ])])]]
makeDtDefs sign = delDoubles . (mapMaybe $ makeDtDef sign)
  where
  delDoubles xs = delDouble xs []
  delDouble [] _  = []
  delDouble (x:xs) sortList = let (Type s _a _b) = fst (head x) in
      if (length sortList) ==
         (length (addSortList s sortList)) then
        delDouble xs sortList
      else
        (x:(delDouble xs (s:sortList)))
  addSortList x xs = (List.nub (x :xs))

makeDtDef :: CASL.Sign.Sign f e -> Named (FORMULA f) ->
             Maybe [(Typ,[(VName,[Typ])])]
makeDtDef sign nf = case sentence nf of
  Sort_gen_ax constrs True -> Just(map makeDt srts) where
    (srts,ops,_maps) = recover_Sort_gen_ax constrs
    makeDt s = (transSort s, map makeOp (filter (hasTheSort s) ops))
    makeOp opSym = (transOP_SYMB sign opSym, transArgs opSym)
    hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot
    hasTheSort _ _ = error "CFOL2IsabelleHOL.hasTheSort"
    transArgs (Qual_op_name _ ot _) = map transSort $ args_OP_TYPE ot
    transArgs _ = error "CFOL2IsabelleHOL.transArgs"
  _ -> Nothing

transSort :: SORT -> Typ
transSort s = Type (showIsaTypeT s baseSign) [] []

transOpType :: OpType -> Typ
transOpType ot = mkCurryFunType (map transSort $ opArgs ot)
                 $ transSort (opRes ot)

transPredType :: PredType -> Typ
transPredType pt = mkCurryFunType (map transSort $ predArgs pt) boolType

------------------------------ Formulas ------------------------------

var :: String -> Term
--(c) var v = IsaSign.Free v noType isaTerm
var v = IsaSign.Free (mkVName v) noType

transVar :: VAR -> String
transVar v = showIsaConstT (simpleIdToId v) baseSign

quantifyIsa :: String -> (String, Typ) -> Term -> Term
quantifyIsa q (v,t) phi =
  App (conDouble q) (Abs (Free (mkVName v) noType) t phi NotCont) NotCont
--(c) App (Const q noType isaTerm) (Abs (Cont v noType isaTerm) t phi NotCont)
--(c) NotCont
--quantifyIsa :: String -> (String, Typ) -> Term -> Term
--quantifyIsa q (v,t) phi =
-- App (Const q) (Abs [(Free v, t)] phi NotCont) NotCont

quantify :: QUANTIFIER -> (VAR, SORT) -> Term -> Term
quantify q (v,t) phi  =
  quantifyIsa (qname q) (transVar v, transSort t) phi
  where
  qname Universal = allS
  qname Existential = exS
  qname Unique_existential = ex1S

transOP_SYMB :: CASL.Sign.Sign f e -> OP_SYMB -> VName
transOP_SYMB sign (Qual_op_name op ot _) = let
  ga = globAnnos sign
  l = length $ args_OP_TYPE ot in
  case (do ots <- Map.lookup op (opMap sign)
           if Set.isSingleton ots
             then return $ mkIsaConstT False ga l op baseSign
             else do
                   i <- List.elemIndex (toOpType ot) (Set.toList ots)
                   return $ mkIsaConstIT False ga l op (i+1) baseSign) of
    Just vn -> vn
    Nothing -> error ("CASL2Isabelle unknown op: " ++ show op)
transOP_SYMB _ (Op_name _) = error "CASL2Isabelle: unqualified operation"

transPRED_SYMB :: CASL.Sign.Sign f e -> PRED_SYMB -> VName
transPRED_SYMB sign (Qual_pred_name p pt@(Pred_type args _) _) = let
  ga = globAnnos sign
  l = length args in
  case (do pts <- Map.lookup p (predMap sign)
           if Set.isSingleton pts
             then return $ mkIsaConstT True ga l p baseSign
             else do
                   i <- List.elemIndex (toPredType pt) (Set.toList pts)
                   return $ mkIsaConstIT True ga l p (i+1) baseSign) of
    Just vn -> vn
    Nothing -> error ("CASL2Isabelle unknown pred: " ++ show p)
transPRED_SYMB _ (Pred_name _) = error "CASL2Isabelle: unqualified predicate"

mapSen :: FormulaTranslator f e -> CASL.Sign.Sign f e -> FORMULA f -> Sentence
mapSen trFrom sign phi = mkSen $ transFORMULA sign trFrom phi

transFORMULA :: CASL.Sign.Sign f e -> FormulaTranslator f e
                -> FORMULA f -> Term
transFORMULA sign tr (Quantification qu vdecl phi _) =
  foldr (quantify qu) (transFORMULA sign tr phi) (flatVAR_DECLs vdecl)
transFORMULA sign tr (Conjunction phis _) =
  if null phis then true
  else foldr1 binConj $ map (transFORMULA sign tr) phis
transFORMULA sign tr (Disjunction phis _) =
  if null phis then false
  else foldr1 binDisj $ map (transFORMULA sign tr) phis
transFORMULA sign tr (Implication phi1 phi2 _ _) =
  binImpl (transFORMULA sign tr phi1) (transFORMULA sign tr phi2)
transFORMULA sign tr (Equivalence phi1 phi2 _) =
  binEqv (transFORMULA sign tr phi1) (transFORMULA sign tr phi2)
transFORMULA sign tr (Negation phi _) =
  termAppl notOp (transFORMULA sign tr phi)
transFORMULA _sign _tr (True_atom _) = true
transFORMULA _sign _tr (False_atom _) = false
transFORMULA sign tr (Predication psymb args _) =
  foldl termAppl
            (con $ transPRED_SYMB sign psymb)
            (map (transTERM sign tr) args)
transFORMULA sign tr (Existl_equation t1 t2 _) | term_sort t1 == term_sort t2 =
  binEq (transTERM sign tr t1) (transTERM sign tr t2)
transFORMULA sign tr (Strong_equation t1 t2 _) | term_sort t1 == term_sort t2 =
  binEq (transTERM sign tr t1) (transTERM sign tr t2)
transFORMULA sign tr (ExtFORMULA phi) =
  tr sign phi
transFORMULA _ _ (Definedness _ _) = true -- totality assumed
transFORMULA _ _ (Membership t s _) | term_sort t == s = true
transFORMULA _ _ _ =
  error "CASL2Isabelle.transFORMULA"

transTERM :: CASL.Sign.Sign f e
             -> (CASL.Sign.Sign f e -> f -> Term) -> TERM f -> Term
transTERM _sign _tr (Qual_var v _s _) =
  var $ transVar v
transTERM sign tr (Application opsymb args _) =
  foldl termAppl
            (con $ transOP_SYMB sign opsymb)
            (map (transTERM sign tr) args)
transTERM sign tr (Conditional t1 phi t2 _) | term_sort t1 == term_sort t2 =
  foldl termAppl (conDouble "If") [transFORMULA sign tr phi,
       transTERM sign tr t1, transTERM sign tr t2]
transTERM sign tr (Sorted_term t s _) | term_sort t == s = transTERM sign tr t
transTERM sign tr (Cast t s _) | term_sort t == s = transTERM sign tr t
transTERM _sign _tr _ =
  error "CFOL2IsabelleHOL.transTERM"
