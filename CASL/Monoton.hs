{- |
Module      :  $Header$
Description :  monotonicities of the overload relation
Copyright   :  (c) C. Maeder DFKI Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

computing the monotonicities for functions and predicates in the overload
relation
-}

module CASL.Monoton (monotonicities) where

import Common.Id
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.AS_Annotation
import Common.Utils

-- CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Overload

monotonicities :: Sign f e -> [Named (FORMULA f)]
monotonicities sig =
    concatMap (makeMonos sig) (Map.toList $ opMap sig)
    ++ concatMap (makePredMonos sig) (Map.toList $ predMap sig)

makeMonos :: Sign f e -> (Id, Set.Set OpType) -> [Named (FORMULA f)]
makeMonos sig (o, ts) = makeEquivMonos o sig $ Set.toList ts

makePredMonos :: Sign f e -> (Id, Set.Set PredType) -> [Named (FORMULA f)]
makePredMonos sig (p, ts) = makeEquivPredMonos p sig $ Set.toList ts

makeEquivMonos :: Id -> Sign f e -> [OpType] -> [Named (FORMULA f)]
makeEquivMonos o sig ts = case ts of
  [] -> []
  t : rs ->
    concatMap (makeEquivMono o sig t) rs ++ makeEquivMonos o sig rs

makeEquivPredMonos :: Id -> Sign f e -> [PredType] -> [Named (FORMULA f)]
makeEquivPredMonos o sig ts = case ts of
  [] -> []
  t : rs ->
    concatMap (makeEquivPredMono o sig t) rs ++ makeEquivPredMonos o sig rs

makeEquivMono :: Id -> Sign f e -> OpType -> OpType -> [Named (FORMULA f)]
makeEquivMono o sig o1 o2 =
      let rs = minimalSupers sig (opRes o1) (opRes o2)
          a1 = opArgs o1
          a2 = opArgs o2
          args = if length a1 == length a2 then
                 combine $ zipWith (maximalSubs sig) a1 a2
                 else []
      in concatMap (makeEquivMonoRs o o1 o2 rs) args

makeEquivMonoRs :: Id -> OpType -> OpType -> [SORT] -> [SORT]
                -> [Named (FORMULA f)]
makeEquivMonoRs o o1 o2 rs args = map (makeEquivMonoR o o1 o2 args) rs

injectVar :: VAR_DECL -> SORT -> TERM f
injectVar = injectTerm . toQualVar

injectTerm :: TERM f -> SORT -> TERM f
injectTerm t s = if sortOfTerm t == s then t else Sorted_term t s nullRange

makeEquivMonoR :: Id -> OpType -> OpType -> [SORT] -> SORT
               -> Named (FORMULA f)
makeEquivMonoR o o1 o2 args res =
    let vds = map (\ (s, n) -> Var_decl [mkNumVar "x" n] s nullRange)
              $ number args
        a1 = zipWith injectVar vds $ opArgs o1
        a2 = zipWith injectVar vds $ opArgs o2
        t1 = injectTerm (Application (Qual_op_name o (toOP_TYPE o1)
                                            nullRange) a1 nullRange) res
        t2 = injectTerm (Application (Qual_op_name o (toOP_TYPE o2)
                                            nullRange) a2 nullRange) res
    in makeNamed "ga_function_monotonicity" $ mkForall vds
           (Strong_equation t1 t2 nullRange) nullRange

makeEquivPredMono :: Id -> Sign f e -> PredType -> PredType
                  -> [Named (FORMULA f)]
makeEquivPredMono o sig o1 o2 =
      let a1 = predArgs o1
          a2 = predArgs o2
          args = if length a1 == length a2 then
                 combine $ zipWith (maximalSubs sig) a1 a2
                 else []
      in map (makeEquivPred o o1 o2) args

makeEquivPred :: Id -> PredType -> PredType -> [SORT] -> Named (FORMULA f)
makeEquivPred o o1 o2 args =
    let vds = map (\ (s, n) -> Var_decl [mkNumVar "x" n] s nullRange)
              $ number args
        a1 = zipWith injectVar vds $ predArgs o1
        a2 = zipWith injectVar vds $ predArgs o2
        t1 = Predication (Qual_pred_name o (toPRED_TYPE o1) nullRange) a1
             nullRange
        t2 = Predication (Qual_pred_name o (toPRED_TYPE o2) nullRange) a2
             nullRange
    in makeNamed "ga_predicate_monotonicity" $ mkForall vds
           (Equivalence t1 t2 nullRange) nullRange
