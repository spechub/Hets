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
import HasCASL.PrintAs()
import HasCASL.Le

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.PrettyPrint
import Common.Id
import Common.Lib.State
import Common.Result

import Data.List as List
import Data.Maybe

-- | bound vars
genVarsOf :: Type -> [(Id, RawKind)]
genVarsOf = map snd . leaves (<0)

-- | vars or other ids 
leaves :: (Int -> Bool) -> Type -> [(Int, (Id, RawKind))]
leaves b t = 
    case t of 
           TypeName j k i -> if b(i)
                             then [(i, (j, k))]
                             else []
           TypeAppl t1 t2 -> leaves b t1 `List.union` leaves b t2
           ExpandedType _ t2 -> leaves b t2
           KindedType tk _ _ -> leaves b tk
           LazyType tl _ -> leaves b tl
           ProductType l _ -> foldl List.union [] $ map (leaves b) l
           FunType t1 _ t2 _ -> leaves b t1 `List.union` leaves b t2
           _ -> error ("leaves: " ++ show t)

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

freshVar :: [Pos] -> State Int (Id, Int)
freshVar ps = do 
    c <- inc
    return (simpleIdToId $ Token ("_var_" ++ show c) ps, c)

mkSingleSubst :: (Id, RawKind) -> State Int Type
mkSingleSubst (i, rk) = do 
    (ty, c) <- freshVar $ posOfId i
    return $ TypeName ty rk c

mkSubst :: [(Id, RawKind)] -> State Int [Type]
mkSubst = mapM mkSingleSubst
                   
type Subst = Map.Map Int Type

eps :: Subst
eps = Map.empty

class Unifiable a where
    subst :: Subst -> a -> a
    match :: TypeMap -> (TypeId -> TypeId -> Bool) 
          -> (Bool, a) -> (Bool, a) -> Result Subst

-- | most general unifier via 'match' 
-- where both sides may contribute substitutions
mgu :: Unifiable a => TypeMap -> a -> a -> Result Subst
mgu tm a b = match tm (==) (True, a) (True, b)

shapeMatch :: Unifiable a => TypeMap -> a -> a -> Result Subst
shapeMatch tm a b = match tm (const $ const True) (True, a) (True, b)

unify :: Unifiable a => TypeMap -> a -> a -> Bool
unify tm a b = isJust $ maybeResult $ mgu tm a b 

subsume :: Unifiable a => TypeMap -> a -> a -> Bool
subsume tm a b = 
    isJust $ maybeResult $ match tm (==) (False, a) (True, b)

equalSubs :: Unifiable a => TypeMap -> a -> a -> Bool
equalSubs tm a b = subsume tm a b && subsume tm b a

idsOf :: (Int -> Bool) -> Type -> Set.Set TypeId
idsOf b = Set.fromList . map (fst . snd) . leaves b

instance Unifiable Type where
    subst m = rename (\ i k n -> 
               case Map.lookup n m of
               Just s -> s
               _ -> TypeName i k n)
    match tm rel t1 (b2, ExpandedType _ t2) = match tm rel t1 (b2, t2)
    match tm rel (b1, ExpandedType _ t1) t2 = match tm rel (b1, t1) t2
    match tm rel t1 (b2, LazyType t2 _) = match tm rel t1 (b2, t2)
    match tm rel (b1, LazyType t1 _) t2 = match tm rel (b1, t1) t2
    match tm rel t1 (b2, KindedType t2 _ _) = match tm rel t1 (b2, t2)
    match tm rel (b1, KindedType t1 _ _) t2 = match tm rel (b1, t1) t2
    match _ rel (b1, t1@(TypeName i1 _k1 v1)) (b2, t2@(TypeName i2 _k2 v2)) =
        if rel i1 i2 && v1 == v2
           then return eps
        else if v1 > 0 && b1 then return $ 
                Map.singleton v1 t2
                else if v2 > 0 && b2 then return $
                     Map.singleton v2 t1
                        else uniResult "typename" t1 
                                    "is not unifiable with typename" t2
    match _tm _ (b1, TypeName i1 _ v1) (_, t2) =
        if v1 > 0 && b1 then 
           if null $ leaves (==v1) t2 then 
              return $ Map.singleton v1 t2
           else uniResult "var" i1 "occurs in" t2
        else uniResult "typename" i1  
                            "is not unifiable with type" t2
    match tm rel t2 t1@(_, TypeName _ _ _) = match tm rel t1 t2
    match tm rel (b1, TypeAppl t1 t2) (b2, TypeAppl t3 t4) = 
        match tm rel (b1, (t1, t2)) (b2, (t3, t4))
    match tm rel (b1, ProductType p1 _) (b2, ProductType p2 _) = 
        match tm rel (b1, p1) (b2, p2)
    match tm rel (b1, FunType t1 _ t2 _) (b2, FunType t3 _ t4 _) = 
        match tm rel (b1, (t1, t2)) (b2, (t3, t4))
    match _ _ (_,t1) (_,t2) = uniResult "type" t1  
                            "is not unifiable with type" t2

showPrettyWithPos :: (PrettyPrint a, PosItem a) => a -> ShowS
showPrettyWithPos a =  let p = get_pos a in
        showChar '\'' . showPretty a . showChar '\'' 
           . noShow (null p) (showChar ' ' . 
               showParen True (showPos $ maximumBy comparePos p))

uniResult :: (PrettyPrint a, PosItem a, PrettyPrint b, PosItem b) =>
              String -> a -> String -> b -> Result Subst
uniResult s1 a s2 b = 
      Result [Diag Hint ("in type\n" ++ "  " ++ s1 ++ " " ++
                         showPrettyWithPos a "\n  " ++ s2 ++ " " ++
                         showPrettyWithPos b "") []] Nothing

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where  
    subst s (t1, t2) = (subst s t1, subst s t2)
    match tm rel (b1, (t1, t2)) (b2, (t3, t4)) =
        let r1@(Result _ m1) = match tm rel (b1, t1) (b2, t3) in
           case m1 of
               Nothing -> r1
               Just s1 -> let r2@(Result _ m2) = match tm rel 
                                   (b1, if b1 then subst s1 t2 else t2)
                                   (b2, if b2 then subst s1 t4 else t4)
                              in case m2 of 
                                     Nothing -> r2
                                     Just s2 -> return $ compSubst s1 s2

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable [a] where
    subst s = map (subst s) 
    match _ _ (_, []) (_, []) = return eps
    match tm rel (b1, a1:r1) (b2, a2:r2) = 
        match tm rel (b1, (a1, r1)) (b2, (a2, r2))
    match tm rel (b1, []) l = match tm rel l (b1, [])
    match _ _ (_, (a:_)) (_, []) = uniResult "type component" a 
                       "is not unifiable with the empty list" 
                       (mkSimpleId "[]")

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable (Maybe a) where
    subst s = fmap (subst s) 
    match _ _ (_, Nothing) _ = return eps
    match _ _ _ (_, Nothing) = return eps
    match tm rel (b1, Just a1) (b2, Just a2) = match tm rel (b1, a1) (b2, a2)

-- | make representation of bound variables unique
generalize :: [TypeArg] -> Type -> Type
generalize tArgs = 
    subst $ Map.fromList $ zipWith 
          ( \ (TypeArg i _ rk c _ _) n -> 
                (c, TypeName i rk n)) tArgs [-1, -2..] 

genTypeArgs :: [TypeArg] -> [TypeArg]
genTypeArgs tArgs = snd $ mapAccumL ( \ n (TypeArg i vk rk _ s ps) ->
                               (n-1, TypeArg i (case vk of 
     Downset t -> Downset $ generalize tArgs t
     _ -> vk) rk n s ps)) (-1) tArgs
                                                
