{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   substitution and unification of types
-}

module HasCASL.Unify where

import HasCASL.As
import HasCASL.AsUtils
import Common.PrettyPrint
import Common.Id
import HasCASL.Le
import Common.Lib.State
import qualified Common.Lib.Map as Map
import Common.Result
import Data.List
import Data.Maybe

varsOf :: Type -> [TypeArg]
varsOf t = 
    case t of 
	   TypeName j k i -> if i > 0 then [TypeArg j k Other []] else []
	   TypeAppl t1 t2 -> varsOf t1 ++ varsOf t2
	   TypeToken _ -> []
	   BracketType _ l _ -> concatMap varsOf l
	   KindedType tk _ _ -> varsOf tk
	   MixfixType l -> concatMap varsOf l
	   LazyType tl _ -> varsOf tl
	   ProductType l _ -> concatMap varsOf l
	   FunType t1 _ t2 _ -> varsOf t1 ++ varsOf t2


generalize :: TypeScheme -> TypeScheme
generalize (TypeScheme vs q@(_ :=> ty) ps) =
    TypeScheme (nub (varsOf ty ++ vs)) q ps

compSubst :: Subst -> Subst -> Subst
compSubst s1 s2 = Map.union (Map.map (subst s2) s1) s2  

mUnify :: TypeMap -> Maybe Type -> Type -> Result Subst
mUnify tm mt ty = unify tm mt (Just ty)

-- | unifiability of type schemes including instantiation with fresh variables 
-- and looking up type aliases
isUnifiable :: TypeMap -> Int -> TypeScheme -> TypeScheme -> Bool
isUnifiable tm c sc1 sc2 = isJust $ maybeResult $ fst $
			   runState (unifIable tm sc1 sc2) c

-- | lift 'State' Int to 'State' Env
toEnvState :: State Int a -> State Env a 
toEnvState p = 
    do s <- get
       let (r, c) = runState p $ counter s
       put s { counter = c }
       return r 

unifIable :: TypeMap -> TypeScheme -> TypeScheme -> State Int (Result Subst)
unifIable tm sc1 sc2 =
    do t1 <- freshInst sc1
       t2 <- freshInst sc2
       return $ unify tm t1 t2

-- -------------------------------------------------------------------------
freshInst :: TypeScheme -> State Int Type
freshInst (TypeScheme tArgs (_ :=> t) _) = 
    do m <- mkSubst tArgs 
       return $ subst m t

freshVar :: State Int Id 
freshVar = 
    do c <- get
       put (c + 1)
       return $ simpleIdToId $ mkSimpleId ("_var_" ++ show c)

mkSingleSubst :: TypeArg -> State Int Subst
mkSingleSubst tv@(TypeArg _ k _ _) =
    do ty <- freshVar
       return $ Map.single tv $ TypeName ty k 1

mkSubst :: [TypeArg] -> State Int Subst
mkSubst tas = do ms <- mapM mkSingleSubst tas
		 return $ Map.unions ms
 		   
type Subst = Map.Map TypeArg Type

eps :: Subst
eps = Map.empty

instance Ord TypeArg where
    TypeArg v1 _ _ _ <= TypeArg v2 _ _ _
	= v1 <= v2

class Unifiable a where
    subst :: Subst -> a -> a
    unify :: TypeMap -> a -> a -> Result Subst

instance Unifiable Type where
    subst m t = case t of
	   TypeName i k _ -> 
	       case Map.lookup (TypeArg i k Other []) m of
	       Just s -> s
	       _ -> t
	   TypeAppl t1 t2 ->
	       TypeAppl (subst m t1) (subst m t2)
	   TypeToken _ -> t
	   BracketType b l ps ->
	       BracketType b (map (subst m) l) ps
	   KindedType tk k ps -> 
	       KindedType (subst m tk) k ps
	   MixfixType l -> MixfixType $ map (subst m) l
	   LazyType tl ps -> LazyType (subst m tl) ps
	   ProductType l ps -> ProductType (map (subst m) l) ps
           FunType t1 a t2 ps -> FunType (subst m t1) a (subst m t2) ps
			-- lookup type aliases
    unify tm t1 (LazyType t2 _) = unify tm t1 t2
    unify tm (LazyType t1 _) t2 = unify tm t1 t2
    unify tm t1 (KindedType t2 _ _) = unify tm t1 t2
    unify tm (KindedType t1 _ _) t2 = unify tm t1 t2
    unify tm t1@(TypeName i1 k1 v1) t2@(TypeName i2 k2 v2) =
	if i1 == i2 then return eps
	else if v1 > 0 then return $ 
	        Map.single (TypeArg i1 k1 Other []) t2
		else if v2 > 0 then return $
		     Map.single (TypeArg i2 k2 Other []) t1
			else let (a1, b1) = expandAlias tm t1 
				 (a2, b2) = expandAlias tm t2 in
			if b1 || b2 then unify tm a1 a2
			   else Result [mkDiag Hint 
					("type '" ++ showId i1 
					 "' is not unifiable with") i2]
					Nothing
    unify tm t1@(TypeName i1 k1 v1) t2 =
	if v1 > 0 then 
	   if i1 `occursIn` t2 then 
	      Result [mkDiag Hint 
			       ("var '" ++ showId i1 
				"' occurs in") t2] Nothing
	   else return $
			Map.single (TypeArg i1 k1 Other []) t2
	else let (a1, b1) = expandAlias tm t1 in
		 if b1 then unify tm a1 t2
		   else Result 
			    [mkDiag Hint 
			     ("type '" ++ showId i1 
			      "' is not unifiable with") t2] Nothing
    unify tm t2 t1@(TypeName _ _ _) = unify tm t1 t2
    unify tm t12@(TypeAppl t1 t2) t34@(TypeAppl t3 t4) = 
	let (ta, a) = expandAlias tm t12
	    (tb, b) = expandAlias tm t34 in
	   if a || b then unify tm ta tb
	      else unify tm (t1, t2) (t3, t4)
    unify tm (ProductType p1 _) (ProductType p2 _) = unify tm p1 p2
    unify tm (FunType t1 _ t2 _) (FunType t3 _ t4 _) = 
	unify tm (t1, t2) (t3, t4)
    unify _ t1 t2 = Result [mkDiag Hint 
			    ("type '" ++ showPretty t1 
			     "' is not unifiable with") t2] Nothing

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where  
    subst s (t1, t2) = (subst s t1, subst s t2)
    unify tm (t1, t2) (t3, t4) =
	let r1@(Result _ m1) = unify tm t1 t3 in
	   case m1 of
	       Nothing -> r1
	       Just s1 -> let r2@(Result _ m2) =
				 unify tm (subst s1 t2) (subst s1 t4) in
			     case m2 of 
				     Nothing -> r2
				     Just s2 -> return $ compSubst s1 s2

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable [a] where
    subst s = map (subst s) 
    unify _ [] [] = return eps
    unify tm (a1:r1) (a2:r2) = unify tm (a1, r1) (a2, r2)
    unify tm [] l = unify tm l [] 
    unify _ (a:_) [] = Result [mkDiag Hint 
			 ("unification failed at") a] Nothing

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable (Maybe a) where
    subst s = fmap (subst s) 
    unify _ Nothing _ = return eps
    unify _ _ Nothing = return eps
    unify tm (Just a1) (Just a2) = unify tm a1 a2

occursIn :: TypeId -> Type -> Bool
occursIn i t = 
    case t of 
	   TypeName j _ _ -> i == j
	   TypeAppl t1 t2 -> occursIn i t1 || occursIn i t2
	   TypeToken tk -> i == simpleIdToId tk 
	   BracketType _ l _ -> any (occursIn i) l
	   KindedType tk _ _ -> occursIn i tk
	   MixfixType l -> any (occursIn i) l
	   LazyType tl _ -> occursIn i tl
	   ProductType l _ -> any (occursIn i) l
	   FunType t1 _ t2 _ -> occursIn i t1 || occursIn i t2

expandAlias :: TypeMap -> Type -> (Type, Bool)
expandAlias tm t = 
    let (ps, as, ta, b) = expandAliases tm t in
       if b && length ps == length as then
	  (subst (Map.fromList (zip ps $ reverse as)) ta, b)
	  else (ta, b)

expandAliases :: TypeMap -> Type -> ([TypeArg], [Type], Type, Bool)
expandAliases tm t@(TypeName i _ _) =
       case Map.lookup i tm of 
            Just (TypeInfo _ _ _ 
		  (AliasTypeDefn (TypeScheme l (_ :=> ts) _))) ->
		     (l, [], ts, True)
	    Just (TypeInfo _ _ _
		  (Supertype _ (TypeScheme l (_ :=> ts) _) _)) ->
		     (l, [], ts, True)
	    _ -> ([], [], t, False)

expandAliases tm (TypeAppl t1 t2) =
    let (ps, as, ta, b) = expandAliases tm t1 
	(t3, b2) = expandAlias tm t2
	in if b then 
	  (ps, t3:as, ta, b)  -- reverse later on
	  else ([], [], TypeAppl t1 t3, b2)

expandAliases tm (FunType  t1 a t2 ps) =
    let (t3, b1) = expandAlias tm t1 
	(t4, b2) = expandAlias tm t2
	in ([], [], FunType  t3 a t4 ps, b1 || b2)

expandAliases tm (ProductType ts ps) =
    let tls = map (expandAlias tm) ts 
	in ([], [], ProductType (map fst tls) ps, any snd tls)

expandAliases tm (LazyType t ps) =
    let (newT, b) = expandAlias tm t 
	in ([], [], LazyType newT ps, b)

expandAliases tm (KindedType t k ps) =
    let (newT, b) = expandAlias tm t 
	in ([], [], KindedType newT k ps, b)

expandAliases _ t = ([], [], t, False)
