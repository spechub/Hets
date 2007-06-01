{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

substitution and unification of types
-}

module HasCASL.Unify where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs ()
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

-- | bound vars
genVarsOf :: Type -> [(Id, RawKind)]
genVarsOf = map snd . leaves (<0)

-- | composition (reversed: first substitution first!)
compSubst :: Subst -> Subst -> Subst
compSubst s1 s2 = Map.union (Map.map (subst s2) s1) s2

-- | unifiability of type schemes including instantiation with fresh variables
-- (and looking up type aliases)
isUnifiable :: TypeMap -> Int -> TypeScheme -> TypeScheme -> Bool
isUnifiable tm c = asSchemes c (unify tm)

-- | test if second scheme is a substitution instance
instScheme :: TypeMap -> Int -> TypeScheme -> TypeScheme -> Bool
instScheme tm c = asSchemes c (subsume tm)

-- | lift 'State' Int to 'State' Env
toEnvState :: State Int a -> State Env a
toEnvState p =
    do s <- get
       let (r, c) = runState p $ counter s
       put s { counter = c }
       return r

toSchemes :: (Type -> Type -> a) -> TypeScheme -> TypeScheme -> State Int a
toSchemes f sc1 sc2 =
    do t1 <- freshInst sc1
       t2 <- freshInst sc2
       return $ f t1 t2

asSchemes :: Int -> (Type -> Type -> a) -> TypeScheme -> TypeScheme -> a
asSchemes c f sc1 sc2 = fst $ runState (toSchemes f sc1 sc2) c

-- -------------------------------------------------------------------------
freshInst :: TypeScheme -> State Int Type
freshInst (TypeScheme _ t _) =
    do let ls = leaves (< 0) t -- generic vars
           vs = map snd ls
       ts <- mkSubst vs
       return $ subst (Map.fromList $ zip (map fst ls) ts) t

inc :: State Int Int
inc = do
    c <- get
    put (c + 1)
    return c

freshVar :: Range -> State Int (Id, Int)
freshVar ps = do
    c <- inc
    return (simpleIdToId $ Token ("_v" ++ show c) ps, c)

mkSingleSubst :: (Id, RawKind) -> State Int Type
mkSingleSubst (i, rk) = do
    (ty, c) <- freshVar $ posOfId i
    return $ TypeName ty rk c

mkSubst :: [(Id, RawKind)] -> State Int [Type]
mkSubst = mapM mkSingleSubst

type Subst = Map.Map Int Type

eps :: Subst
eps = Map.empty

flatKind :: Type -> RawKind
flatKind = mapKindV (const InVar) id . rawKindOfType

match :: TypeMap -> (TypeId -> TypeId -> Bool)
          -> (Bool, Type) -> (Bool, Type) -> Result Subst
match tm rel p1@(b1, ty1) p2@(b2, ty2) = 
  if flatKind ty1 == flatKind ty2 then case (ty1, ty2) of
    (_, ExpandedType _ t2) -> match tm rel p1 (b2, t2)
    (ExpandedType _ t1, _) -> match tm rel (b1, t1) p2
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
           (superIds tm i2) then return eps
        else if b1 && not b2 && v1 == 0 && v2 == 0 && Set.member i2
           (superIds tm i1) then return eps
        else uniResult "typename" ty1 "is not unifiable with typename" ty2
    (TypeName _ _ v1, _) ->
        if v1 > 0 && b1 then
           if null $ leaves (==v1) ty2 then
              return $ Map.singleton v1 ty2
           else uniResult "var" ty1 "occurs in" ty2
        else uniResult "typename" ty1
                            "is not unifiable with type" ty2
    (_, TypeName _ _ _) -> match tm rel p2 p1
    (TypeAppl f1 a1, TypeAppl f2 a2) -> 
      let res = do
            s1 <- match tm rel (b1, f1) (b2, f2)
            s2 <- match tm rel (b1, if b1 then subst s1 a1 else a1)
                   (b2, if b2 then subst s1 a2 else a2)
            return $ compSubst s1 s2
          res1@(Result _ ms1) = if hasRedex ty1 then
              match tm rel (b1, redStep ty1) (b2, ty2)
              else fail "match1"
          res2@(Result _ ms2) = if hasRedex ty2 then
              match tm rel (b1, ty1) (b2, redStep ty2)
              else fail "match2"
      in case ms1 of
               Nothing -> case ms2 of
                   Nothing -> res 
                   Just _ -> res2
               Just _ -> res1
    _ -> if ty1 == ty2 then return eps else 
             uniResult "type" ty1 "is not unifiable with type" ty2
  else uniResult "type" ty1 "is not unifiable with differently kinded type" ty2

-- | most general unifier via 'match'
-- where both sides may contribute substitutions
mgu :: TypeMap -> Type -> Type -> Result Subst
mgu tm a b = match tm (==) (True, a) (True, b)

mguList :: TypeMap -> [Type] -> [Type] -> Result Subst
mguList tm l1 l2 = case (l1, l2) of
    ([], []) -> return eps
    (h1 : t1, h2 : t2) -> do
       s1 <- mgu tm h1 h2
       s2 <- mguList tm (map (subst s1) t1) $ map (subst s1) t2
       return $ compSubst s1 s2
    _ -> mkError "no unification of differently long argument lists"
         (head $ l1 ++ l2)

shapeMatch :: TypeMap -> Type -> Type -> Result Subst
shapeMatch tm a b = match tm (const $ const True) (True, a) (True, b)

unify :: TypeMap -> Type -> Type -> Bool
unify tm a b = isJust $ maybeResult $ mgu tm a b

subsume :: TypeMap -> Type -> Type -> Bool
subsume tm a b =
    isJust $ maybeResult $ match tm (==) (False, a) (True, b)

equalSubs :: TypeMap -> Type -> Type -> Bool
equalSubs tm a b = subsume tm a b && subsume tm b a

subst :: Subst -> Type -> Type
subst m = rename (\ i k n ->
               case Map.lookup n m of
               Just s -> s
               _ -> TypeName i k n)

showDocWithPos :: Type -> ShowS
showDocWithPos a =  let p = getRange a in
        showChar '\'' . showDoc a . showChar '\''
           . noShow (isNullRange p) (showChar ' ' .
               showParen True (showPos $ maximumBy comparePos (rangeToList p)))

uniResult :: String -> Type -> String -> Type -> Result Subst
uniResult s1 a s2 b =
      Result [Diag Hint ("in type\n" ++ "  " ++ s1 ++ " " ++
                         showDocWithPos a "\n  " ++ s2 ++ " " ++
                         showDocWithPos b "") nullRange] Nothing

-- | make representation of bound variables unique
generalize :: [TypeArg] -> Type -> Type
generalize tArgs =
    subst $ Map.fromList $ zipWith
          ( \ (TypeArg i _ _ rk c _ _) n ->
                (c, TypeName i rk n)) tArgs [-1, -2..]

genTypeArgs :: [TypeArg] -> [TypeArg]
genTypeArgs tArgs = snd $ mapAccumL ( \ n (TypeArg i v vk rk _ s ps) ->
                               (n-1, TypeArg i v (case vk of
     Downset t -> Downset $ generalize tArgs t
     _ -> vk) rk n s ps)) (-1) tArgs

