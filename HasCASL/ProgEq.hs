{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

   convert some formulas to program equations
-}

module HasCASL.ProgEq where

import Common.Result
import Common.Id
import qualified Common.Lib.Set as Set

import HasCASL.As
import HasCASL.Le
import HasCASL.VarDecl
import HasCASL.Builtin
import HasCASL.AsUtils

isOp :: OpInfo -> Bool
isOp o = case opDefn o of
                    NoOpDefn _ -> True
                    Definition _ _ -> True
                    SelectData _ _ -> True
                    _ -> False

isOpKind :: (OpInfo -> Bool) -> Env -> Term -> Bool
isOpKind f e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isOpKind f e trm
    QualOp _ (InstOpId i _ _) sc _ -> 
        if i `elem` map fst bList then False else 
           let mi = findOpId e i sc in case mi of
                    Nothing -> False
                    Just oi -> f oi
    _ -> False

isVar, isConstrAppl, isPat, isLHS, isExecutable :: Env -> Term -> Bool

isOfType :: TypeQual -> Bool
isOfType q = case q of
             OfType -> True
             Inferred -> True
             AsType -> False
             InType -> False

isVar e t = case t of 
    TypedTerm trm q _ _  -> isOfType q && isVar e trm
    QualVar _ -> True
    _ -> False

isConstrAppl e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isConstrAppl e trm
    ApplTerm t1 t2 _ -> isConstrAppl e t1 && isPat e t2
    _ -> isOpKind isConstructor e t

isPat e t = case t of 
    TypedTerm trm q _ _ -> isOfType q && isPat e trm
    TupleTerm ts _ -> all (isPat e) ts
    AsPattern _ p _ -> isPat e p
    _ -> isVar e t || isConstrAppl e t

isLHS e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isLHS e trm
    ApplTerm t1 t2 _ -> isLHS e t1 && isPat e t2
    _ -> isOpKind isOp e t

isExecutable e t = 
    case t of 
    QualVar _ -> True
    QualOp _ _ _ _ -> True
    QuantifiedTerm _ _ _ _ -> False
    TypedTerm _ InType _ _ -> False
    TypedTerm trm _ _ _ -> isExecutable e trm
    ApplTerm t1 t2 _ -> isExecutable e t1 && isExecutable e t2
    TupleTerm ts _ -> all (isExecutable e) ts
    LambdaTerm ps _ trm _ -> all (isPat e) ps && isExecutable e trm
    CaseTerm trm ps _ -> isExecutable e trm &&
       all ( \ (ProgEq p c _) -> isPat e p && isExecutable e c) ps
    LetTerm _ ps trm _ -> all ( \ (ProgEq p c _) -> 
           (isPat e p || isLHS e p) && isExecutable e c) ps
           && isExecutable e trm
    _ -> error "isExecutable"

mkProgEq, mkCondEq, mkConstTrueEq, mkQuantEq :: Env -> Term -> Maybe ProgEq
mkProgEq e t = case getTupleAp t of
    Just (i, [a, b]) -> 
       let cond p r = 
             let pvs = map getVar $ extractVars p
                 rvs = map getVar $ extractVars r
             in isLHS e p && isExecutable e r && 
                 null (checkUniqueness pvs) && 
                      Set.fromList rvs `Set.subset` Set.fromList pvs 
       in if i `elem` [eqId, exEq, eqvId] then 
              if cond a b
                 then Just $ ProgEq a b $ get_pos i
                 else if cond a b then Just $ ProgEq a b $ get_pos i
                      else mkConstTrueEq e t
          else mkConstTrueEq e t
    _ -> case getAppl t of 
        Just (i, _, [f]) -> if i `elem` [notId, negId] then
            case mkConstTrueEq e f of
            Just (ProgEq p _ ps) -> Just $ ProgEq p 
                (mkQualOp falseId unitType []) ps
            Nothing -> Nothing
            else mkConstTrueEq e t
        _ -> mkConstTrueEq e t

mkConstTrueEq e t = 
    let vs = map getVar $ extractVars t in
        if isLHS e t && null (checkUniqueness vs) then
           Just $ ProgEq t (mkQualOp trueId unitType []) $ get_pos t
           else Nothing

bottom :: Term
bottom = mkQualOp botId botType []

mkCondEq e t = case getTupleAp t of
    Just (i, [p, r]) -> 
        if i == implId then mkCond e p r 
        else if i == infixIf then mkCond e r p
        else mkProgEq e t
    _ -> mkProgEq e t
    where
    mkCond env f p = case mkProgEq env p of 
      Just (ProgEq lhs rhs ps) -> 
          let pvs = map getVar $ extractVars lhs
              fvs = map getVar $ extractVars f 
          in if isExecutable env f &&
             Set.fromList fvs `Set.subset` Set.fromList pvs then
             Just (ProgEq lhs 
                   (mkTerm whenElse whenType [] 
                    $ TupleTerm [rhs, f, bottom] []) ps)
             else Nothing
      Nothing -> Nothing

mkQuantEq e t = case t of 
    QuantifiedTerm Universal _ trm _ -> mkQuantEq e trm
    -- ignore quantified variables
    -- do not allow conditional equations
    _ -> mkCondEq e t
        
getTupleAp :: Term -> Maybe (Id, [Term])
getTupleAp t = case getAppl t of
   Just (i, _, [tu]) -> case getTupleArgs tu of
       Just ts -> Just (i, ts)
       Nothing -> Nothing
   _ -> Nothing

getTupleArgs :: Term -> Maybe [Term]    
getTupleArgs t = case t of
    TypedTerm trm qt _ _ -> case qt of 
      InType -> Nothing
      _ -> getTupleArgs trm
    TupleTerm ts _ -> Just ts
    _ -> Nothing

translateSen :: Env -> Sentence -> Sentence
translateSen env s = case s of 
        Formula t -> case mkQuantEq env t of
                 Nothing -> s 
                 Just pe@(ProgEq p _ _) -> case getAppl p of
                     Nothing -> s 
                     Just (i, sc, _) -> ProgEqSen i sc pe
        _ -> s 
