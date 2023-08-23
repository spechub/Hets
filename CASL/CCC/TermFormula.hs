{- |
Module      :  ./CASL/CCC/TermFormula.hs
Description :  auxiliary functions on terms and formulas
Copyright   :  (c) Mingyi Liu, Till Mossakowski, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Auxiliary functions on terms and formulas
-}

module CASL.CCC.TermFormula where

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Overload
import CASL.Quantification
import CASL.Sign
import CASL.ToDoc
import CASL.Utils

import Common.Id
import Common.Result

import Control.Monad

import Data.Function
import Data.List
import Data.Maybe

import qualified Data.Map as Map
import qualified Data.Set as Set

-- | the sorted term is always ignored
unsortedTerm :: TERM f -> TERM f
unsortedTerm t = case t of
  Sorted_term t' _ _ -> unsortedTerm t'
  Cast t' _ _ -> unsortedTerm t'
  _ -> t

-- | check whether it exist a (unique)existent quantification
isExQuanti :: FORMULA f -> Bool
isExQuanti f = case f of
  Quantification Universal _ f' _ -> isExQuanti f'
  Quantification {} -> True
  Relation f1 _ f2 _ -> isExQuanti f1 || isExQuanti f2
  Negation f' _ -> isExQuanti f'
  _ -> False

-- | check whether it contains a membership formula
isMembership :: FORMULA f -> Bool
isMembership f = case f of
  Quantification _ _ f' _ -> isMembership f'
  Junction _ fs _ -> any isMembership fs
  Negation f' _ -> isMembership f'
  Relation f1 _ f2 _ -> isMembership f1 || isMembership f2
  Membership {} -> True
  _ -> False

-- | check whether it contains a definedness formula
containDef :: FORMULA f -> Bool
containDef f = case f of
  Quantification _ _ f' _ -> containDef f'
  Junction _ fs _ -> any containDef fs
  Relation f1 _ f2 _ -> containDef f1 || containDef f2
  Negation f' _ -> containDef f'
  Definedness _ _ -> True
  _ -> False

-- | check whether it contains a negation
containNeg :: FORMULA f -> Bool
containNeg f = case f of
  Quantification _ _ f' _ -> containNeg f'
  Relation _ c f' _ | c /= Equivalence -> containNeg f'
  Relation f' Equivalence _ _ -> containNeg f'
  Negation _ _ -> True
  _ -> False

domainDef :: FORMULA f -> Maybe (TERM f, FORMULA f)
domainDef f = case stripAllQuant f of
  Relation (Definedness t _) Equivalence f' _
    | not (containDef f') -> Just (t, f')
  _ -> Nothing

-- | check whether it is a Variable
isVar :: TERM t -> Bool
isVar t = case unsortedTerm t of
  Qual_var {} -> True
  _ -> False

-- | extract all variables of a term
varOfTerm :: Ord f => TERM f -> [TERM f]
varOfTerm t = case unsortedTerm t of
  Qual_var {} -> [t]
  Application _ ts _ -> concatMap varOfTerm ts
  _ -> []

-- | extract all arguments of a term
arguOfTerm :: TERM f -> [TERM f]
arguOfTerm = snd . topIdOfTerm

nullId :: ((Id, Int), [TERM f])
nullId = ((stringToId "", 0), [])

topIdOfTerm :: TERM f -> ((Id, Int), [TERM f])
topIdOfTerm t = case unsortedTerm t of
  Application o ts _ -> ((opSymbName o, length ts), ts)
  _ -> nullId

-- | get the patterns of a axiom
patternsOfAxiom :: FORMULA f -> [TERM f]
patternsOfAxiom = snd . topIdOfAxiom

topIdOfAxiom :: FORMULA f -> ((Id, Int), [TERM f])
topIdOfAxiom f = case stripAllQuant f of
    Negation f' _ -> topIdOfAxiom f'
    Relation _ c f' _ | c /= Equivalence -> topIdOfAxiom f'
    Relation f' Equivalence _ _ -> topIdOfAxiom f'
    Predication p ts _ -> ((predSymbName p, length ts), ts)
    Equation t _ _ _ -> topIdOfTerm t
    Definedness t _ -> topIdOfTerm t
    _ -> nullId

-- | split the axiom into condition and rest axiom
splitAxiom :: FORMULA f -> ([FORMULA f], FORMULA f)
splitAxiom f = case stripAllQuant f of
                     Relation f1 c f2 _ | c /= Equivalence ->
                       let (f3, f4) = splitAxiom f2 in (f1 : f3, f4)
                     f' -> ([], f')

-- | get the premise of a formula, without implication return true
conditionAxiom :: FORMULA f -> FORMULA f
conditionAxiom = conjunct . fst . splitAxiom

-- | get the conclusion of a formula, without implication return the formula
restAxiom :: FORMULA f -> FORMULA f
restAxiom = snd . splitAxiom

-- | get right hand side of an equivalence, without equivalence return true
resultAxiom :: FORMULA f -> FORMULA f
resultAxiom f = case restAxiom f of
                  Relation _ Equivalence f' _ -> f'
                  _ -> trueForm

-- | get right hand side of an equation, without equation return dummy term
resultTerm :: FORMULA f -> TERM f
resultTerm f = case restAxiom f of
                 Negation (Definedness _ _) _ ->
                   varOrConst (mkSimpleId "undefined")
                 Equation _ _ t _ -> t
                 _ -> varOrConst (mkSimpleId "unknown")

getSubstForm :: (FormExtension f, TermExtension f, Ord f) => Sign f e
  -> FORMULA f -> FORMULA f
  -> Result ((Subst f, [FORMULA f]), (Subst f, [FORMULA f]))
getSubstForm sig f1 f2 = do
  let p1 = patternsOfAxiom f1
      p2 = patternsOfAxiom f2
      getVars = Set.map fst . freeVars sig . stripAllQuant
  getSubst sig (p1, getVars f1) (p2, getVars f2)

mkCast :: SORT -> TERM f -> SORT -> (TERM f, [FORMULA f])
mkCast s2 t s1 = if s1 == s2 then (t, []) else
  case unsortedTerm t of
    Qual_var v _ r -> (Qual_var v s1 r, [])
    _ -> (Cast t s1 nullRange, [Membership t s1 nullRange])

mkSortedTerm :: SORT -> TERM f -> SORT -> TERM f
mkSortedTerm s1 t s2 = if s1 == s2 then t else
  case unsortedTerm t of
    Qual_var v _ r -> Qual_var v s2 r
    _ -> Sorted_term t s2 nullRange

minSortTerm :: TermExtension f => TERM f -> TERM f
minSortTerm t = case t of
  Sorted_term st _ _ -> case optTermSort st of
    Nothing -> t
    Just _ -> minSortTerm st
  _ -> t

mkSTerm :: TermExtension f => Sign f e -> SORT -> TERM f
  -> (TERM f, [FORMULA f])
mkSTerm sig s t =
  let s2 = fromMaybe s $ optTermSort t
      t0 = minSortTerm t
      s0 = fromMaybe s $ optTermSort t0
  in case maximalSubs sig s s2 of
    l@(s1 : _) -> let
      s3 = if s0 == s2 then s1 else
           fromMaybe s1 $ find (leqSort sig s0) l
      (s4, fs) = mkCast s2 t s3
      in (mkSortedTerm s3 s4 s, fs)
    _ -> error $ "CCC.mkSTerm " ++ show (s0, s, s2)

getSubst :: (FormExtension f, TermExtension f, Ord f) => Sign f e
  -> ([TERM f], Set.Set VAR) -> ([TERM f], Set.Set VAR)
  -> Result ((Subst f, [FORMULA f]), (Subst f, [FORMULA f]))
getSubst sig (p1, vs1) (p2, vs2) =
  let getVars = Set.map fst . freeTermVars sig
  in case (p1, p2) of
    ([], []) -> do
      let i = Set.intersection vs1 vs2
      unless (Set.null i)
        $ appendDiags [mkDiag Warning "possibly conflicting variables" i]
      return ((Map.empty, []), (Map.empty, []))
    (hd1 : tl1, hd2 : tl2) ->
      let r = getSubst sig (tl1, vs1) (tl2, vs2)
          mkS1 v1 s1 = do
              let (hd3, fs) = mkSTerm sig s1 hd2
              ((m1, fs1), m2) <- getSubst sig
                (tl1, Set.delete v1 vs1) (tl2, vs2)
              return ((Map.insert v1 hd3 m1, fs ++ fs1), m2)
          mkS2 v2 s2 = do
              let (hd3, fs) = mkSTerm sig s2 hd1
              (m1, (m2, fs2)) <- getSubst sig (tl1, vs1)
                (tl2, Set.delete v2 vs2)
              return (m1, (Map.insert v2 hd3 m2, fs ++ fs2))
          cond v vs hd = Set.member v vs && Set.notMember v (getVars hd)
          diag v = appendDiags [mkDiag Warning
                            "unsupported occurrence of variable" v] >> r
      in case (unsortedTerm hd1, unsortedTerm hd2) of
        (Qual_var v1 s1 _, Qual_var v2 s2 _)
          | v1 == v2 && s1 == s2 -> getSubst sig (tl1, Set.delete v1 vs1)
               (tl2, Set.delete v2 vs2)
          | Set.member v1 vs2 ->
            if Set.member v2 vs1
            then appendDiags [mkDiag Warning
                            ("unsupported mix of variables '"
                             ++ show v1 ++ "' and") v2] >> r
            else mkS1 v1 s1
          | otherwise -> mkS2 v2 s2
        (Qual_var v1 s1 _, _) ->
            if cond v1 vs2 hd2 then diag v1
            else mkS1 v1 s1
        (_, Qual_var v2 s2 _) ->
            if cond v2 vs1 hd1 then diag v2
            else mkS2 v2 s2
        (_, _) | sameOpsApp sig hd1 hd2 ->
             getSubst sig (arguOfTerm hd1 ++ tl1, vs1)
                          (arguOfTerm hd2 ++ tl2, vs2)
        _ -> mkError "no overlap at" hd1
    _ -> error "non-matching leading terms"

-- | extract defined subsorts
isSubsortDef :: FORMULA f -> Maybe (SORT, VAR_DECL, FORMULA f)
isSubsortDef f = case f of
  Quantification Universal [vd@(Var_decl [v] super _)]
    (Relation (Membership (Qual_var v2 super2 _) sub _) Equivalence f1 _) _
     | (v, super) == (v2, super2) -> Just (sub, vd, f1)
  _ -> Nothing

-- | create the obligations for subsorts
infoSubsorts :: Set.Set SORT -> [(SORT, VAR_DECL, FORMULA f)] -> [FORMULA f]
infoSubsorts emptySorts = map (\ (_, v, f) -> mkExist [v] f)
  . filter (\ (s, _, _) -> not $ Set.member s emptySorts)

-- | extract the leading symbol from a formula
leadingSym :: GetRange f => FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym = fmap extractLeadingSymb . leadingTermPredication

-- | extract the leading symbol with the range from a formula
leadingSymPos :: GetRange f => FORMULA f
  -> (Maybe (Either (TERM f) (FORMULA f)), Range)
leadingSymPos f = leading (f, False, False, False) where
  -- three booleans to indicate inside implication, equivalence or negation
  leadTerm t q = case unsortedTerm t of
    a@(Application _ _ p) -> (Just (Left a), p)
    _ -> (Nothing, q)
  leading (f1, b1, b2, b3) = case (stripAllQuant f1, b1, b2, b3) of
    (Negation f' _, _, _, False) ->
        leading (f', b1, b2, True)
    (Relation _ c f' _, _, False, False)
        | c /= Equivalence ->
        leading (f', True, False, False)
    (Relation f' Equivalence _ _, _, False, False) ->
        leading (f', b1, True, False)
    (Definedness t q, _, _, _) -> leadTerm t q
    (pr@(Predication _ _ p), _, _, _) ->
        (Just (Right pr), p)
    (Equation t _ _ q, _, False, False) -> leadTerm t q
    _ -> (Nothing, getRange f1)

-- | extract the leading term or predication from a formula
leadingTermPredication :: GetRange f => FORMULA f
  -> Maybe (Either (TERM f) (FORMULA f))
leadingTermPredication = fst . leadingSymPos

-- | extract the leading symbol from a term or a formula
extractLeadingSymb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extractLeadingSymb lead = case lead of
  Left (Application os _ _) -> Left os
  Right (Predication p _ _) -> Right p
  _ -> error "CASL.CCC.TermFormula<extractLeadingSymb>"

-- | replaces variables by terms in a term or formula
substRec :: Eq f => [(TERM f, TERM f)] -> Record f (FORMULA f) (TERM f)
substRec subs = (mapRecord id)
   { foldQual_var = \ t _ _ _ -> subst subs t } where
  subst l tt = case l of
    [] -> tt
    (n, v) : r -> if tt == v then n else subst r tt

substitute :: Eq f => [(TERM f, TERM f)] -> TERM f -> TERM f
substitute = foldTerm . substRec

substiF :: Eq f => [(TERM f, TERM f)] -> FORMULA f -> FORMULA f
substiF = foldFormula . substRec

sameOpTypes :: Sign f e -> OP_TYPE -> OP_TYPE -> Bool
sameOpTypes sig = on (leqF sig) toOpType

sameOpSymbs :: Sign f e -> OP_SYMB -> OP_SYMB -> Bool
sameOpSymbs sig o1 o2 = on (==) opSymbName o1 o2 && case (o1, o2) of
  (Qual_op_name _ t1 _, Qual_op_name _ t2 _) -> sameOpTypes sig t1 t2
  _ -> False

-- | check whether two terms are the terms of same application symbol
sameOpsApp :: Sign f e -> TERM f -> TERM f -> Bool
sameOpsApp sig app1 app2 = case (unsortedTerm app1, unsortedTerm app2) of
  (Application o1 _ _, Application o2 _ _) -> sameOpSymbs sig o1 o2
  _ -> False

eqPattern :: Sign f e -> TERM f -> TERM f -> Bool
eqPattern sig t1 t2 = case (unsortedTerm t1, unsortedTerm t2) of
  (Qual_var v1 _ _, Qual_var v2 _ _) -> v1 == v2
  _ | sameOpsApp sig t1 t2 ->
    and $ on (zipWith $ eqPattern sig) arguOfTerm t1 t2
  _ -> False
