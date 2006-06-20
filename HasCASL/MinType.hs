
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

choose a minimal type

-}

module HasCASL.MinType where

import HasCASL.As
import HasCASL.TypeAna

q2p :: (a, b, c, d) -> (c, d)
q2p (_, _, c, d) = (c,d)

typeNub :: TypeEnv -> (a -> (Type, Term)) -> [a] -> [a]
typeNub te f l = case l of 
    [] -> []
    x : xs -> if any (flip comp (f x) . f) xs then typeNub te f xs 
              else x : typeNub te f (filter (not . comp (f x) . f) xs)
    where
    comp :: (Type, Term) -> (Type, Term) -> Bool
    comp (ty1, t1) (ty2, t2) = eqTerm t1 t2 && 
                               lesserType te ty1 ty2

eqTerm :: Term -> Term -> Bool
eqTerm t1 t2 = case (t1, t2) of
     (TypedTerm t _ _ _, _) -> eqTerm t t2 
     (_, TypedTerm t _ _ _) -> eqTerm t1 t
     (QualVar (VarDecl v1 _s1 _ _), QualVar (VarDecl v2 _s2 _ _)) -> 
         v1 == v2 
     (QualOp _ (InstOpId i1 _ _) _ _, QualOp _ (InstOpId i2 _ _) _ _) -> 
         i1 == i2
     (ApplTerm tf1 ta1 _, ApplTerm tf2 ta2 _) -> 
         eqTerm tf1 tf2 && eqTerm ta1 ta2
     (TupleTerm ts1 _, TupleTerm ts2 _) -> 
         length ts1 == length ts2 && and (zipWith eqTerm ts1 ts2)
     (QuantifiedTerm q1 vs1 f1 _, QuantifiedTerm q2 vs2 f2 _) -> 
         (q1, vs1) == (q2, vs2) && eqTerm f1 f2
     (LambdaTerm ps1 p1 f1 _, LambdaTerm ps2 p2 f2 _) -> 
          and (zipWith eqTerm ps1 ps2) && p1 == p2 && eqTerm f1 f2
          && length ps1 == length ps2
     (CaseTerm f1 e1 _, CaseTerm f2 e2 _) -> 
         eqTerm f1 f2 && length e1 == length e2 && and (zipWith eqProgEq e1 e2)
     (LetTerm _ e1 f1 _, LetTerm _ e2 f2 _) -> 
         eqTerm f1 f2 && length e1 == length e2 && and (zipWith eqProgEq e1 e2)
     _ -> False

eqProgEq :: ProgEq -> ProgEq -> Bool
eqProgEq (ProgEq p1 t1 _) (ProgEq p2 t2 _) = eqTerm p1 p2 && eqTerm t1 t2
