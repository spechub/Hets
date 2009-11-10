{- |
Module      :  $Header$
Description :  generalized unification of types
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

substitution and unification of types
-}

module HasCASL.Unify where

import HasCASL.As
import HasCASL.FoldType
import HasCASL.AsUtils
import HasCASL.PrintAs ()
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.Le

import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.DocUtils
import Common.Id
import Common.Lib.State
import Common.Result

import Data.List as List
import Data.Maybe

-- | composition (reversed: first substitution first!)
compSubst :: Subst -> Subst -> Subst
compSubst s1 s2 = Map.union (Map.map (subst s2) s1) s2

-- | test if second scheme is a substitution instance
instScheme :: TypeMap -> Int -> TypeScheme -> TypeScheme -> Bool
instScheme tm c = asSchemes c (subsume tm)

specializedScheme :: ClassMap -> [TypeArg] -> [TypeArg] -> Bool
specializedScheme cm args1 args2 = length args1 == length args2 && and
    (zipWith (\ (TypeArg _ v1 vk1 _ _ _ _) (TypeArg _ v2 vk2 _ _ _ _) ->
        (v1 == v2 || v1 == NonVar) && case (vk1, vk2) of
          (VarKind k1, VarKind k2) -> lesserKind cm k1 k2
          _ -> vk1 == vk2) args1 args2)

-- | lift 'State' Int to 'State' Env
toEnvState :: State Int a -> State Env a
toEnvState p = do
    s <- get
    let (r, c) = runState p $ counter s
    put s { counter = c }
    return r

toSchemes :: (Type -> Type -> a) -> TypeScheme -> TypeScheme -> State Int a
toSchemes f sc1 sc2 = do
    (t1, _) <- freshInst sc1
    (t2, _) <- freshInst sc2
    return $ f t1 t2

asSchemes :: Int -> (Type -> Type -> a) -> TypeScheme -> TypeScheme -> a
asSchemes c f sc1 sc2 = fst $ runState (toSchemes f sc1 sc2) c

substTypeArg :: Subst -> TypeArg -> VarKind
substTypeArg s (TypeArg _ _ vk _ _ _ _) = case vk of
    Downset super -> Downset $ substGen s super
    _ -> vk

mapArgs :: Subst -> [(Id, Type)] -> [TypeArg] -> [(Type, VarKind)]
mapArgs s ts = foldr ( \ ta l ->
    maybe l ( \ (_, t) -> (t, substTypeArg s ta) : l) $
            find ( \ (j, _) -> getTypeVar ta == j) ts) []

freshInst :: TypeScheme -> State Int (Type, [(Type, VarKind)])
freshInst (TypeScheme tArgs t _) = do
    let ls = leaves (< 0) t -- generic vars
        vs = map snd ls
    ts <- mkSubst vs
    let s = Map.fromList $ zip (map fst ls) ts
    return (substGen s t, mapArgs s (zip (map fst vs) ts) tArgs)

inc :: State Int Int
inc = do
    c <- get
    put (c + 1)
    return c

freshVar :: Id -> State Int (Id, Int)
freshVar i@(Id ts _ _) = do
    c <- inc
    return (Id [mkSimpleId $ "_v" ++ show c ++ case ts of
                  [t] -> '_' : dropWhile (== '_') (tokStr t)
                  _ -> ""] [] $ posOfId i, c)

mkSingleSubst :: (Id, RawKind) -> State Int Type
mkSingleSubst (i, rk) = do
    (ty, c) <- freshVar i
    return $ TypeName ty rk c

mkSubst :: [(Id, RawKind)] -> State Int [Type]
mkSubst = mapM mkSingleSubst

type Subst = Map.Map Int Type

eps :: Subst
eps = Map.empty

flatKind :: Type -> RawKind
flatKind = nonVarRawKind . rawKindOfType

noAbs :: Type -> Bool
noAbs t = case t of
    TypeAbs _ _ _ -> False
    _ -> True

match :: TypeMap -> (Id -> Id -> Bool)
      -> (Bool, Type) -> (Bool, Type) -> Result Subst
match tm rel p1@(b1, ty1) p2@(b2, ty2) =
  if flatKind ty1 == flatKind ty2 then case (ty1, ty2) of
    (_, ExpandedType _ t2) | noAbs t2 -> match tm rel p1 (b2, t2)
    (ExpandedType _ t1, _) | noAbs t1 -> match tm rel (b1, t1) p2
    (_, TypeAppl (TypeName l _ _) t2) | l == lazyTypeId ->
              match tm rel p1 (b2, t2)
    (TypeAppl (TypeName l _ _) t1, _) | l == lazyTypeId ->
              match tm rel (b1, t1) p2
    (_, KindedType t2 _ _) -> match tm rel p1 (b2, t2)
    (KindedType t1 _ _, _) -> match tm rel (b1, t1) p2
    (TypeName i1 _k1 v1, TypeName i2 _k2 v2) ->
        if rel i1 i2 && v1 == v2
           then return eps
        else if v1 > 0 && b1 then return $ Map.singleton v1 ty2
        else if v2 > 0 && b2 then return $ Map.singleton v2 ty1
{- the following two conditions only guarantee that instScheme also matches for
   a partial function that is mapped to a total one.
   Maybe a subtype condition is better. -}
        else if not b1 && b2 && v1 == 0 && v2 == 0 && Set.member i1
                  (superIds tm i2)
             || b1 && not b2 && v1 == 0 && v2 == 0 && Set.member i2
                  (superIds tm i1) then return eps
        else uniResult "typename" ty1 "is not unifiable with typename" ty2
    (TypeName _ _ v1, _) -> case redStep ty2 of
      Just ry2 -> match tm rel p1 (b2, ry2)
      Nothing ->
        if v1 > 0 && b1 then
           if null $ leaves (==v1) ty2 then
              return $ Map.singleton v1 ty2
           else uniResult "var" ty1 "occurs in" ty2
        else uniResult "typename" ty1
                            "is not unifiable with type" ty2
    (_, TypeName _ _ _) -> match tm rel p2 p1
    (TypeAppl f1 a1, TypeAppl f2 a2) -> case redStep ty1 of
       Just ry1 -> match tm rel (b1, ry1) p2
       Nothing -> case redStep ty2 of
         Just ry2 -> match tm rel p1 (b2, ry2)
         Nothing -> do
            s1 <- match tm rel (b1, f1) (b2, f2)
            s2 <- match tm rel (b1, if b1 then subst s1 a1 else a1)
                   (b2, if b2 then subst s1 a2 else a2)
            return $ compSubst s1 s2
    _ -> if ty1 == ty2 then return eps else
             uniResult "type" ty1 "is not unifiable with type" ty2
  else uniResult "type" ty1 "is not unifiable with differently kinded type" ty2

shapeMatch :: TypeMap -> Type -> Type -> Result Subst
shapeMatch tm a b = match tm (const $ const True) (True, a) (True, b)

subsume :: TypeMap -> Type -> Type -> Bool
subsume tm a b =
    isJust $ maybeResult $ match tm (==) (False, a) (True, b)

-- | substitute generic variables with negative index
substGen :: Subst -> Type -> Type
substGen m = foldType mapTypeRec
  { foldTypeName = \ t _ _ n -> if n >= 0 then t else case Map.lookup n m of
      Just s -> s
      Nothing -> t
  , foldTypeAbs = \ t v1@(TypeArg _ _ _ _ c _ _) ty p ->
      if Map.member c m then substGen (Map.delete c m) t else TypeAbs v1 ty p }

getTypeOf :: Monad m => Term -> m Type
getTypeOf trm = case trm of
    TypedTerm _ q t _ -> return $ case q of
        InType -> unitType
        _ -> t
    QualVar (VarDecl _ t _ _) -> return t
    QualOp _ _ (TypeScheme _ t _) is _ _ -> return $
        substGen (Map.fromList $ zip [-1, -2..] is) t
    TupleTerm ts ps -> if null ts then return unitType else do
        tys <- mapM getTypeOf ts
        return $ mkProductTypeWithRange tys ps
    QuantifiedTerm _ _ t _ -> getTypeOf t
    LetTerm _ _ t _ -> getTypeOf t
    AsPattern _ p _ -> getTypeOf p
    _ -> fail $ "getTypeOf: " ++ showDoc trm ""

-- | substitute variables with positive index
subst :: Subst -> Type -> Type
subst m = if Map.null m then id else foldType mapTypeRec
  { foldTypeName = \ t _ _ n -> if n <= 0 then t else case Map.lookup n m of
      Just s -> s
      Nothing -> t }

showDocWithPos :: Type -> ShowS
showDocWithPos a = let p = getRange a in
    showChar '\'' . showDoc a . showChar '\''
    . noShow (isNullRange p) (showChar ' ' .
        showParen True (showPos $ maximum (rangeToList p)))

uniResult :: String -> Type -> String -> Type -> Result Subst
uniResult s1 a s2 b = Result [Diag Hint ("in type\n" ++ "  " ++ s1 ++ " " ++
    showDocWithPos a "\n  " ++ s2 ++ " " ++
    showDocWithPos b "") nullRange] Nothing

-- | make representation of bound variables unique
generalize :: [TypeArg] -> Type -> Type
generalize tArgs = subst $ Map.fromList $ zipWith
    ( \ (TypeArg i _ _ rk c _ _) n -> (c, TypeName i rk n)) tArgs [-1, -2..]

genTypeArgs :: [TypeArg] -> [TypeArg]
genTypeArgs tArgs = snd $ mapAccumL ( \ n (TypeArg i v vk rk _ s ps) ->
    (n - 1, TypeArg i v (case vk of
      Downset t -> Downset $ generalize tArgs t
      _ -> vk) rk n s ps)) (-1) tArgs
