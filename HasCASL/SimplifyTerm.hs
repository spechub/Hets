{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

remove type annotations of unique variables or operations

-}

module HasCASL.SimplifyTerm where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.VarDecl
import HasCASL.Le
import qualified Common.Lib.Map as Map
import Common.Lib.State

-- | remove qualification of unique identifiers
simplifyTerm :: Env -> Term -> Term
simplifyTerm env trm = case trm of
   QualVar (VarDecl v _ _ ps) -> if Map.member v $ assumps env then
         trm else ResolvedMixTerm v [] ps
   QualOp _ (InstOpId i _ _) _ ps -> 
       if Map.member i $ localVars env then trm else 
          case Map.lookup i $ assumps env of 
          Just (OpInfos [_]) -> ResolvedMixTerm i [] ps
          _ -> trm
   ApplTerm t1 t2 ps ->
       ApplTerm (simplifyTerm env t1) (simplifyTerm env t2) ps
   TupleTerm ts ps -> TupleTerm (map (simplifyTerm env) ts) ps
   TypedTerm te q ty ps -> let 
      nt = simplifyTerm env te 
      ntyped = TypedTerm nt q ty ps 
      in case q of
      InType -> ntyped
      AsType -> ntyped
      _ -> case nt of 
           QualVar (VarDecl v oty _ qs) | oty == ty -> 
              if Map.member v $ assumps env then ntyped
              else TypedTerm (ResolvedMixTerm v [] qs) OfType ty ps
           QualOp _ (InstOpId i _ _) _ qs | q == Inferred ->
              if Map.member i $ localVars env then ntyped
              else TypedTerm (ResolvedMixTerm i [] qs) OfType ty ps
           _ -> ntyped
   QuantifiedTerm q vs te ps -> 
       let nEnv = execState (mapM_ ( \ vd -> 
              case vd of 
              GenVarDecl v -> addLocalVar False v
              _ -> return ()) vs) env
       in QuantifiedTerm q vs (simplifyTerm nEnv te) ps
   LambdaTerm ps p te qs -> 
       let nEnv = execState (mapM_ (addLocalVar False) 
                     $ concatMap extractVars ps) env
       in LambdaTerm (map (simplifyTerm env) ps) p (simplifyTerm nEnv te) qs
   CaseTerm te es ps -> 
       CaseTerm (simplifyTerm env te) (map (simplifyEq env) es) ps
   LetTerm b es te ps ->
       let addEqVars = mapM_ ( \ (ProgEq p _ _) -> 
                       mapM_ (addLocalVar False) $ extractVars p)
           nEnv = execState (addEqVars es) env
       in LetTerm b (map (simplifyEq nEnv) es) (simplifyTerm nEnv te) ps
   AsPattern vd pa ps -> AsPattern vd (simplifyTerm env pa) ps
   TermToken _ -> trm
   MixfixTerm ts -> MixfixTerm $ map (simplifyTerm env) ts
   BracketTerm b ts ps -> BracketTerm b (map (simplifyTerm env) ts) ps
   MixTypeTerm q ty ps -> MixTypeTerm q ty ps  
   ResolvedMixTerm i ts ps -> ResolvedMixTerm i (map (simplifyTerm env) ts) ps
  
simplifyEq :: Env -> ProgEq -> ProgEq
simplifyEq env (ProgEq p t r) = 
    let nEnv = execState (mapM_ (addLocalVar False) $ extractVars p) env
        q = simplifyTerm env p 
        s = simplifyTerm nEnv t 
    in ProgEq q s r

simplifySentence :: Env -> Sentence -> Sentence
simplifySentence env s = case s of
    Formula t -> Formula $ simplifyTerm env t
    ProgEqSen i sc eq -> ProgEqSen i sc $ simplifyEq env eq
    _ -> s

