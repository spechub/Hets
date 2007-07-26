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

simplifyRec :: Env -> MapRec
simplifyRec env = mapRec
    { foldQualVar = \ t (VarDecl v _ _ ps) ->
      if Map.member v $ assumps env then t else ResolvedMixTerm v [] [] ps
    , foldQualOp = \ trm _ i _ _ ps ->
      if Map.member i $ localVars env then trm else
          case Map.lookup i $ assumps env of
          Just s | hasMany s -> trm
          _ -> ResolvedMixTerm i [] [] ps
    , foldTypedTerm = \ _ nt q ty ps ->
        let ntyped = TypedTerm nt q ty ps in case q of
        InType -> ntyped
        AsType -> ntyped
        _ -> case nt of
           QualVar (VarDecl v oty _ qs) | oty == ty ->
              if Map.member v $ assumps env then ntyped
              else TypedTerm (ResolvedMixTerm v [] [] qs) OfType ty ps
           QualOp _ i _ _ qs | q == Inferred ->
              if Map.member i $ localVars env then ntyped
              else TypedTerm (ResolvedMixTerm i [] [] qs) OfType ty ps
           _ -> ntyped
    , foldQuantifiedTerm = \ (QuantifiedTerm q vs te ps) _ _ _ _ ->
       let nEnv = execState (mapM_ ( \ vd ->
              case vd of
              GenVarDecl v -> addLocalVar False v
              _ -> return ()) vs) env
       in QuantifiedTerm q vs (simplifyTerm nEnv te) ps
    , foldLambdaTerm = \ (LambdaTerm ls p te qs) ps _ _ _ ->
       let nEnv = execState (mapM_ (addLocalVar False)
                     $ concatMap extractVars ls) env
       in LambdaTerm ps p (simplifyTerm nEnv te) qs
    , foldLetTerm = \ (LetTerm b es te ps) _ _ _ _ ->
       let addEqVars = mapM_ ( \ (ProgEq p _ _) ->
                       mapM_ (addLocalVar False) $ extractVars p)
           nEnv = execState (addEqVars es) env
       in LetTerm b (map (simplifyEq nEnv) es) (simplifyTerm nEnv te) ps
    , foldProgEq = \ (ProgEq p t r) q _ _ ->
        let nEnv = execState (mapM_ (addLocalVar False) $ extractVars p) env
            s = simplifyTerm nEnv t
        in ProgEq q s r
    }


-- | remove qualification of unique identifiers
simplifyTerm :: Env -> Term -> Term
simplifyTerm = foldTerm . simplifyRec

simplifyEq :: Env -> ProgEq -> ProgEq
simplifyEq = foldEq . simplifyRec

simplifySentence :: Env -> Sentence -> Sentence
simplifySentence env s = case s of
    Formula t -> Formula $ simplifyTerm env t
    ProgEqSen i sc eq -> ProgEqSen i sc $ simplifyEq env eq
    _ -> s

