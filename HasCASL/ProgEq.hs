{- |
Module      :  $Header$
Description :  convert some formulas to program equations
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

convert some formulas to program equations
-}

module HasCASL.ProgEq where

import Common.Result
import Common.Id
import qualified Data.Map as Map
import qualified Data.Set as Set

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.Unify (getTypeOf)
import HasCASL.MinType (haveCommonSupertype)

isOp :: OpInfo -> Bool
isOp o = case opDefn o of
    NoOpDefn _ -> True
    Definition _ _ -> True
    SelectData _ _ -> True
    _ -> False

isOpKind :: (OpInfo -> Bool) -> Env -> Term -> Bool
isOpKind f e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isOpKind f e trm
    QualOp _ (PolyId i _ _) sc _ _ _ ->
        if i `elem` map fst bList then False else
           any (\ oi -> f oi && let sc2 = opType oi in
                         sc == sc2 || haveCommonSupertype e sc sc2)
              $ Set.toList $ Map.findWithDefault Set.empty i $ assumps e
    _ -> False

isOfType :: TypeQual -> Bool
isOfType q = case q of
    OfType -> True
    Inferred -> True
    AsType -> False
    InType -> False

isVar :: Env -> Term -> Bool
isVar e t = case t of
    TypedTerm trm q _ _  -> isOfType q && isVar e trm
    QualVar _ -> True
    _ -> False

isConstrAppl :: Env -> Term -> Bool
isConstrAppl e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isConstrAppl e trm
    ApplTerm t1 t2 _ -> isConstrAppl e t1 && isPat e t2
    _ -> isOpKind isConstructor e t

isPat :: Env -> Term -> Bool
isPat e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isPat e trm
    TupleTerm ts _ -> all (isPat e) ts
    AsPattern _ p _ -> isPat e p
    _ -> isVar e t || isConstrAppl e t

isLHS :: Env -> Term -> Bool
isLHS e t = case t of
    TypedTerm trm q _ _ -> isOfType q && isLHS e trm
    ApplTerm t1 t2 _ -> isLHS e t1 && isPat e t2
    _ -> isOpKind isOp e t

isExecutable :: Env -> Term -> Bool
isExecutable e t = case t of
    QualVar _ -> True
    QualOp _ _ _ _ _ _ -> True
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

mkProgEq :: Env -> Term -> Maybe ProgEq
mkProgEq e t = case getTupleAp t of
    Just (i, [a, b]) ->
       let cond p r =
             let pvs = map getVar $ extractVars p
                 rvs = map getVar $ extractVars r
             in isLHS e p && isExecutable e r &&
                 null (checkUniqueness pvs) &&
                      Set.fromList rvs `Set.isSubsetOf` Set.fromList pvs
       in if i `elem` [eqId, exEq, eqvId] then
              if cond a b
                 then Just $ ProgEq a b $ getRange i
                 else if cond b a then Just $ ProgEq b a $ getRange i
                      else mkConstTrueEq e t
          else mkConstTrueEq e t
    _ -> case getAppl t of
        Just (i, _, [f]) -> if i `elem` [notId, negId] then
            case mkConstTrueEq e f of
            Just (ProgEq p _ ps) -> Just $ ProgEq p
                (mkQualOp falseId unitTypeScheme [] nullRange) ps
            Nothing -> Nothing
            else mkConstTrueEq e t
        _ -> mkConstTrueEq e t

mkConstTrueEq :: Env -> Term -> Maybe ProgEq
mkConstTrueEq e t =
    let vs = map getVar $ extractVars t in
        if isLHS e t && null (checkUniqueness vs) then
           Just $ ProgEq t (mkQualOp trueId unitTypeScheme [] nullRange)
                    $ getRange t
           else Nothing

bottom :: Type -> Term
bottom ty = mkQualOp botId botType [ty] nullRange

mkCondEq :: Env -> Term -> Maybe ProgEq
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
          in case getTypeOf rhs of
          Nothing -> Nothing
          Just ty -> if isExecutable env f &&
             Set.fromList fvs `Set.isSubsetOf` Set.fromList pvs then
             Just (ProgEq lhs
                   (mkTerm whenElse whenType [ty] nullRange
                    $ TupleTerm [rhs, f, bottom ty] nullRange) ps)
             else Nothing
      Nothing -> Nothing

mkQuantEq :: Env -> Term -> Maybe ProgEq
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

translateSen :: Env -> Sentence -> Sentence
translateSen env s = case s of
        Formula t -> case mkQuantEq env t of
                 Nothing -> s
                 Just pe@(ProgEq p _ _) -> case getAppl p of
                     Nothing -> s
                     Just (i, sc, _) -> ProgEqSen i sc pe
        _ -> s
