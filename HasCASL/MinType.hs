
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

choose one (or more) minimal/maximal typings

-}

module HasCASL.MinType where

import Common.AS_Annotation
import Common.PrettyPrint

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna

import Debug.Trace

q2p :: (a, b, c, d) -> (c, d)
q2p (_, _, c, d) = (c,d)

typeNub :: Bool -> TypeMap -> (a -> (Type, Term)) -> [a] -> [a]
typeNub b tm f l = 
  case l of 
       [] -> []
       x : xs -> (if any ( \ y -> case comp (f x) (f y) of
                                  Lower -> not b
                                  Higher -> b
                                  BothDirections -> True
                                  NoDirection -> False) xs then [] else [x]) 
                     ++ typeNub b tm f xs
  where
  comp :: (Type, Term) -> (Type, Term) -> PrecRel
  comp (ty1, t1) (ty2, t2) = 
    if eqTerm t1 t2 then let r = lesserType tm ty2 ty1 in
       if lesserType tm ty1 ty2 then
          if r then BothDirections
          else Lower
       else if r then Higher 
            else NoDirection
    else NoDirection

eqTerm :: Term -> Term -> Bool
eqTerm t1 t2 = case (t1, t2) of
     (TypedTerm t OfType _ _, _) -> eqTerm t t2 
     (_, TypedTerm t OfType _ _) -> eqTerm t1 t
     (TypedTerm t AsType _ _, _) -> eqTerm t t2 
     (_, TypedTerm t AsType _ _) -> eqTerm t1 t
     (QualVar (VarDecl v1 _ _ _), QualVar (VarDecl v2 _ _ _)) -> v1 == v2
     (QualOp _ (InstOpId i1 _ _) _ _, QualOp _ (InstOpId i2 _ _) _ _) -> 
         i1 == i2
     (ApplTerm tf1 ta1 _, ApplTerm tf2 ta2 _) -> 
         eqTerm tf1 tf2 && eqTerm ta1 ta2
     (TupleTerm ts1 _, TupleTerm ts2 _) -> 
         length ts1 == length ts2 && and (zipWith eqTerm ts1 ts2)
     _ -> False
