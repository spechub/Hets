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

module HasCASL.MinType
  ( q2p
  , typeNub
  , haveCommonSupertype
  , getCommonSupertype
  ) where

import HasCASL.As
import HasCASL.FoldType
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.TypeAna
import HasCASL.Unify
import HasCASL.Constrain

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Lib.State
import Common.Utils

import Data.List
import Data.Maybe

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
haveCommonSupertype e s = isJust . getCommonSupertype e s

getCommonSupertype :: Env -> TypeScheme -> TypeScheme -> Maybe TypeScheme
getCommonSupertype e s1 s2 =
    evalState (toEnvState $ haveCommonSupertypeE e s1 s2) e

haveCommonSupertypeE :: Env -> TypeScheme -> TypeScheme
  -> State Int (Maybe TypeScheme)
haveCommonSupertypeE eIn s1 s2 = do
    (t1, l1) <- freshInst s1
    (t2, l2) <- freshInst s2
    cst <- mkSingleSubst (genName "commonSupertype", rStar)
    let cs = Set.fromList [Subtyping t1 cst, Subtyping t2 cst]
        e = foldr addToEnv eIn $ (cst, VarKind universe) : l1 ++ l2
    Result _ mr <- shapeRelAndSimplify False e cs (Just cst)
    return $ case mr of
      Nothing -> Nothing
      Just (sbst, rcs) -> let (qs, subC) = partitionC rcs
        in case reduceCommonSubtypes
               (Rel.transClosure $ fromTypeMap $ typeMap e)
               (toListC subC) of
             Just msb | Set.null qs -> let
               ty = subst (compSubst sbst msb) cst
               fvs = freeTVars ty
               svs = sortBy comp fvs
               comp a b = compare (fst a) $ fst b
               tvs = localTypeVars e
               newArgs = map ( \ (_, (i, _)) -> case Map.lookup i tvs of
                  Nothing -> error $ "generalizeS " ++ show (i, ty)
                      ++ "\n" ++ showDoc (s1, s2) ""
                  Just (TypeVarDefn v vk rk c) ->
                      TypeArg i v vk rk c Other nullRange) svs
               in Just $ TypeScheme (genTypeArgs newArgs)
                      (generalize newArgs ty) nullRange
             _ -> Nothing

reduceCommonSubtypes :: Rel.Rel Type -> [(Type, Type)] -> Maybe Subst
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
    subM = mapM (commonSubtype e True . mkPair) csubts
    superM = mapM (commonSubtype e False . mkPair) csuperts
    in case (concat rest2, subM, superM) of
      ([], Just l1, Just l2) -> Just $ Map.fromList $ l1 ++ l2
      _ -> Nothing

commonSubtype :: Rel.Rel Type -> Bool -> (Type, [Type]) -> Maybe (Int, Type)
commonSubtype trel b (ty, l) =
  let tySet = foldl1 Set.intersection
         $ map (if b then Rel.predecessors trel else Rel.succs trel) l
  in case ty of
    TypeName _ _ n | not (Set.null tySet) && n > 0
      -> Just (n, Set.findMin tySet)
    _ -> Nothing
