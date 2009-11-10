{- |
Module      :  $Header$
Description :  choose a minimal type for overloaded terms
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

choose a minimal type
-}

module HasCASL.MinType (q2p, typeNub, haveCommonSupertype) where

import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.TypeAna
import HasCASL.Unify
import HasCASL.Constrain

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.Result
import Common.Lib.State
import Common.Utils

import Data.List

q2p :: (a, b, c, d) -> (c, d)
q2p (_, _, c, d) = (c,d)

typeNub :: Env -> (a -> (Type, Term)) -> [a] -> [a]
typeNub e f = let
    comp (ty1, t1) (ty2, t2) = eqTerm e t1 t2 &&
                               lesserType e ty1 ty2
    lt a b = comp (f a) (f b)
    in keepMins lt

eqTerm :: Env -> Term -> Term -> Bool
eqTerm e t1 t2 = case (t1, t2) of
     (TypedTerm t _ _ _, _) -> eqTerm e t t2
     (_, TypedTerm t _ _ _) -> eqTerm e t1 t
     (QualVar (VarDecl v1 _s1 _ _), QualVar (VarDecl v2 _s2 _ _)) ->
         v1 == v2
     (QualOp _ i1 s1 _ _ _, QualOp _ i2 s2 _ _ _) -> i1 == i2
         && haveCommonSupertype e s1 s2
     (ApplTerm tf1 ta1 _, ApplTerm tf2 ta2 _) ->
         eqTerm e tf1 tf2 && eqTerm e ta1 ta2
     (TupleTerm ts1 _, TupleTerm ts2 _) ->
         length ts1 == length ts2 && and (zipWith (eqTerm e) ts1 ts2)
     (QuantifiedTerm q1 vs1 f1 _, QuantifiedTerm q2 vs2 f2 _) ->
         (q1, vs1) == (q2, vs2) && eqTerm e f1 f2
     (LambdaTerm ps1 p1 f1 _, LambdaTerm ps2 p2 f2 _) ->
          and (zipWith (eqTerm e) ps1 ps2) && p1 == p2 && eqTerm e f1 f2
          && length ps1 == length ps2
     (CaseTerm f1 e1 _, CaseTerm f2 e2 _) ->
         eqTerm e f1 f2 && length e1 == length e2
         && and (zipWith (eqProgEq e) e1 e2)
     (LetTerm _ e1 f1 _, LetTerm _ e2 f2 _) ->
         eqTerm e f1 f2 && length e1 == length e2
         && and (zipWith (eqProgEq e) e1 e2)
     _ -> False

eqProgEq :: Env -> ProgEq -> ProgEq -> Bool
eqProgEq e (ProgEq p1 t1 _) (ProgEq p2 t2 _) = eqTerm e p1 p2 && eqTerm e t1 t2

addToEnv :: (Type, VarKind) -> Env -> Env
addToEnv (ty, vk) e = case ty of
    TypeName i rk c | c > 0 ->
        execState (addLocalTypeVar False (TypeVarDefn NonVar vk rk c) i) e
    _ -> e

haveCommonSupertype :: Env -> TypeScheme -> TypeScheme -> Bool
haveCommonSupertype e s1 s2 =
    evalState (toEnvState $ haveCommonSupertypeE e s1 s2) e

haveCommonSupertypeE :: Env -> TypeScheme -> TypeScheme -> State Int Bool
haveCommonSupertypeE eIn s1 s2 = do
    (t1, l1) <- freshInst s1
    (t2, l2) <- freshInst s2
    cst <- mkSingleSubst (genName "commonSupertype", rStar)
    let cs = Set.fromList [Subtyping t1 cst, Subtyping t2 cst]
        e = foldr addToEnv eIn $ l1 ++ l2
    Result _ mr <- shapeRelAndSimplify False e cs (Just cst)
    return $ case mr of
      Nothing -> False
      Just (_, rcs) -> let (qs, subC) = partitionC rcs
        in Set.null qs
          && reduceCommonSubtypes (Rel.transClosure $ fromTypeMap $ typeMap e)
             (toListC subC)

reduceCommonSubtypes :: Rel.Rel Type -> [(Type, Type)] -> Bool
reduceCommonSubtypes e l = let
    mygroup = groupBy ( \ (a, b) (c, d) -> case (a, b, d) of
                  (TypeName _ _ n, TypeName _ _ 0, TypeName _ _ 0)
                      -> n > 0 && a == c
                  _ -> False)
    mypart = partition ( \ s -> case s of
                         [] -> error "reduceCommonSubtypes1"
                         [_] -> False
                         _ -> True)
    (csubts, rest) = mypart $ mygroup l
    swap = map $ \ (a, b) -> (b, a)
    (csuperts, rest2) = mypart $ mygroup $ sort $ swap (concat rest)
    mkPair s = case s of
          (a, _) : _ -> (a, map snd s)
          _ -> error "reduceCommonSubtypes2"
    in null (concat rest2) && all (commonSubtype e True . mkPair) csubts
           && all (commonSubtype e False . mkPair) csuperts

commonSubtype :: Rel.Rel Type -> Bool -> (Type, [Type]) -> Bool
commonSubtype e b (a, l) = case l of
       [_] -> True
       c : d : r ->
           let c1 = commonSubtype e b (a, c : r)
               c2 = commonSubtype e b (a, d : r)
           in commonSubtypeId e b c d && (c1 || c2)
               || any ( \ f -> commonSubtypeId e b c f
                            && commonSubtypeId e b d f) r
                    && c1 && c2
       _ -> error "commonSubtype"

commonSubtypeId :: Rel.Rel Type -> Bool -> Type -> Type -> Bool
commonSubtypeId e b c d = let tm = Rel.toMap e in
    if b then
       not $ Map.null
           $ Map.filter ( \ s -> Set.member c s && Set.member d s) tm
    else not $ Set.null $ Set.intersection
         (Map.findWithDefault Set.empty c tm)
         $ Map.findWithDefault Set.empty d tm
