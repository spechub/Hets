{- |
Module      :  $Header$
Description :  simplify terms for prettier printing
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

remove type annotations of unique variables or operations

-}

module HasCASL.SimplifyTerm where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.FoldTerm
import qualified Data.Map as Map
import Common.Lib.State

-- | simplify terms and patterns (if True)
simplifyRec :: Bool -> Env -> MapRec
simplifyRec b env = mapRec
    { foldQualVar = \ t (VarDecl v ty _ ps) ->
      if Map.member v (assumps env) then t else
          let nv = ResolvedMixTerm v [] [] ps in
          if b then TypedTerm nv OfType ty ps else nv
    , foldQualOp = \ trm _ (PolyId i _ _) _ tys k ps ->
      if Map.member i $ localVars env then trm else
          case Map.lookup i $ assumps env of
          Just s | hasMany s -> trm
          _ -> ResolvedMixTerm i (if k == Infer then [] else tys) [] ps
    , foldTypedTerm = \ _ nt q ty ps ->
        let ntyped = TypedTerm nt q ty ps in case q of
        InType -> ntyped
        AsType -> ntyped
        _ -> case nt of
           QualVar (VarDecl v oty _ qs) | oty == ty ->
              if Map.member v $ assumps env then nt
              else TypedTerm (ResolvedMixTerm v [] [] qs) q ty ps
           QualOp _ (PolyId i _ _) _ tys k qs | q == Inferred ->
              if Map.member i $ localVars env then ntyped
              else TypedTerm (ResolvedMixTerm i
                     (if k == Infer then [] else tys) [] qs) q ty ps
           TypedTerm ntt qt tyt _ -> case qt of
               InType -> nt
               AsType -> if tyt == ty || q == Inferred then nt else ntyped
               OfType -> if tyt == ty || q == Inferred then nt else ntyped
               Inferred -> TypedTerm ntt q ty ps
           _ -> ntyped
    , foldQuantifiedTerm = \ (QuantifiedTerm q vs te ps) _ _ _ _ ->
       let nEnv = execState (mapM_ ( \ vd ->
              case vd of
              GenVarDecl v -> addLocalVar False v
              _ -> return ()) vs) env
       in QuantifiedTerm q vs (simplifyTerm nEnv te) ps
    , foldLambdaTerm = \ (LambdaTerm ls p te qs) _ _ _ _ ->
       let nEnv = execState (mapM_ (addLocalVar False)
                     $ concatMap extractVars ls) env
       in LambdaTerm (map (simplifyPattern env) ls) p (simplifyTerm nEnv te) qs
    , foldLetTerm = \ (LetTerm br es te ps) _ _ _ _ ->
       let addEqVars = mapM_ ( \ (ProgEq p _ _) ->
                       mapM_ (addLocalVar False) $ extractVars p)
           nEnv = execState (addEqVars es) env
       in LetTerm br (map (simplifyEq nEnv) es) (simplifyTerm nEnv te) ps
    , foldProgEq = \ (ProgEq p t r) q _ _ ->
        let nEnv = execState (mapM_ (addLocalVar False) $ extractVars p) env
            s = simplifyTerm nEnv t
        in ProgEq q s r }

-- | remove qualification of unique identifiers
simplifyTerm :: Env -> Term -> Term
simplifyTerm = foldTerm . simplifyRec False

-- | remove qualification of unique identifiers
simplifyPattern :: Env -> Term -> Term
simplifyPattern = foldTerm . simplifyRec True

simplifyEq :: Env -> ProgEq -> ProgEq
simplifyEq = foldEq . simplifyRec False

simplifySentence :: Env -> Sentence -> Sentence
simplifySentence env s = case s of
    Formula t -> Formula $ simplifyTerm env t
    ProgEqSen i sc eq -> ProgEqSen i sc $ simplifyEq env eq
    _ -> s
