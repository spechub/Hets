
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

choose a minimal type

-}

module HasCASL.MinType where


import Common.Lib.State
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.VarDecl

q2p :: (a, b, c, d) -> (c, d)
q2p (_, _, c, d) = (c,d)

typeNub :: TypeMap -> (a -> (Type, Term)) -> [a] -> [a]
typeNub tm f l = 
  case l of 
       [] -> []
       x : xs -> let rest = typeNub tm f xs in
                 if any ( \ y -> comp (f x) $ f y) xs then rest
                 else x : filter ( \ y -> not $ comp (f y) $ f x) rest 
  where
  comp :: (Type, Term) -> (Type, Term) -> Bool
  comp (ty1, t1) (ty2, t2) = 
    if eqTerm t1 t2 then lesserType tm ty2 ty1
    else False

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
     (QuantifiedTerm q1 vs1 f1 _, QuantifiedTerm q2 vs2 f2 _) -> 
         (q1, vs1) == (q2, vs2) && eqTerm f1 f2
     _ -> False

-- | store assumptions
putLocalVars :: Map.Map Id Type -> State Env ()
putLocalVars vs =  do { e <- get; put e { localVars = vs } }

-- | add a local variable with an analysed type
addLocalVar :: VarDecl -> State Env () 
addLocalVar (VarDecl v t _ _) = 
    do ass <- gets assumps
       vs <- gets localVars
       if Map.member v ass then
          addDiags [mkDiag Hint "variable shadows global name(s)" v]
          else if Map.member v vs then 
          addDiags [mkDiag Hint "shadowing by variable" v]
          else return ()
       putLocalVars $ Map.insert v t vs 

-- | add a local variable with an analysed type
addGenLocalVar :: GenVarDecl -> State Env () 
addGenLocalVar d = case d of 
     GenVarDecl v -> addLocalVar v
     GenTypeVarDecl t -> addTypeVarDecl True t >> return () 

