{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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
import qualified Common.Lib.Set as Set
import Common.Result
import Data.List
import Data.Maybe

-- | vars
varsOf :: Type -> Set.Set TypeArg
varsOf = leaves (>0)

-- | vars or other ids 
leaves :: (Int -> Bool) -> Type -> Set.Set TypeArg
leaves b t = 
    case t of 
	   TypeName j k i -> if b(i)
			     then Set.single $ TypeArg j k Other [] 
			     else Set.empty
	   TypeAppl t1 t2 -> leaves b t1 `Set.union` leaves b t2
	   KindedType tk _ _ -> leaves b tk
	   LazyType tl _ -> leaves b tl
	   ProductType l _ -> Set.unions $ map (leaves b) l
	   FunType t1 _ t2 _ -> leaves b t1 `Set.union` leaves b t2
	   _ -> error ("leaves: " ++ show t)

generalize :: TypeScheme -> TypeScheme
generalize (TypeScheme _ q@(_ :=> ty) ps) =
    TypeScheme (Set.toList $ varsOf ty) q ps

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
freshInst (TypeScheme tArgs (_ :=> t) _) = 
    do m <- mkSubst tArgs 
       return $ subst (Map.fromList m) t

freshVar :: Pos -> State Int Id 
freshVar p = 
    do c <- get
       put (c + 1)
       return $ simpleIdToId $ Token ("_var_" ++ show c) p

mkSingleSubst :: TypeArg -> State Int (TypeArg, Type)
mkSingleSubst tv@(TypeArg _ k _ _) =
    do ty <- freshVar $ posOfTypeArg tv
       return (tv, TypeName ty k 1)

mkSubst :: [TypeArg] -> State Int [(TypeArg, Type)]
mkSubst tas = mapM mkSingleSubst tas
 		   
type Subst = Map.Map TypeArg Type

eps :: Subst
eps = Map.empty

class Unifiable a where
    subst :: Subst -> a -> a
    match :: TypeMap -> (Bool, a) -> (Bool, a) -> Result Subst

-- | most general unifier via 'match' 
-- where both sides may contribute substitutions
mgu :: Unifiable a => TypeMap -> a -> a -> Result Subst
mgu tm a b = match tm (True, a) (True, b)

unify :: Unifiable a => TypeMap -> a -> a -> Bool
unify tm a b = isJust $ maybeResult $ mgu tm a b 

subsume :: Unifiable a => TypeMap -> a -> a -> Bool
subsume tm a b = isJust $ maybeResult $ match tm (False, a) (True, b)

equalSubs :: Unifiable a => TypeMap -> a -> a -> Bool
equalSubs tm a b = subsume tm a b && subsume tm b a

-- | get the type variable
getTypeVar :: TypeArg -> Id
getTypeVar(TypeArg v _ _ _) = v

idsOf :: (Int -> Bool) -> Type -> Set.Set TypeId
idsOf b = Set.image getTypeVar . leaves b

occursIn :: TypeMap -> TypeId -> Type -> Bool
occursIn tm i =  Set.any (relatedTypeIds tm i) . idsOf (const True)

relatedTypeIds :: TypeMap -> TypeId -> TypeId -> Bool
relatedTypeIds tm i1 i2 =  
    not $ Set.disjoint (allRelIds tm i1) $ allRelIds tm i2

allRelIds :: TypeMap -> TypeId -> Set.Set TypeId
allRelIds tm i = Set.union (superIds tm i) $ subIds tm i 

mapType :: IdMap -> Type -> Type
mapType m ty = if Map.isEmpty m then ty else 
	      rename ( \ i k n ->
	       let t = TypeName i k n in
	       if n == 0 then 
		  case Map.lookup i m of
		  Just j -> TypeName j k 0
		  _ -> t
	       else t) ty

rename :: (TypeId -> Kind -> Int -> Type) -> Type -> Type
rename m t = case t of
	   TypeName i k n -> m i k n
	   TypeAppl t1 t2 ->
	       TypeAppl (rename m t1) (rename m t2)
	   TypeToken _ -> t
	   BracketType b l ps ->
	       BracketType b (map (rename m) l) ps
	   KindedType tk k ps -> 
	       KindedType (rename m tk) k ps
	   MixfixType l -> MixfixType $ map (rename m) l
	   LazyType tl ps -> LazyType (rename m tl) ps
	   ProductType l ps -> ProductType (map (rename m) l) ps
           FunType t1 a t2 ps -> FunType (rename m t1) a (rename m t2) ps

instance Unifiable Type where
    subst m = rename (\ i k n -> 
	       case Map.lookup (TypeArg i k Other []) m of
	       Just s -> s
	       _ -> TypeName i k n)
    match m (a, s) (b, t) = mm m (a, unalias m s) (b, unalias m t)
      where 
      mm tm t1 (b2, LazyType t2 _) = mm tm t1 (b2, t2)
      mm tm (b1, LazyType t1 _) t2 = mm tm (b1, t1) t2
      mm tm t1 (b2, KindedType t2 _ _) = mm tm t1 (b2, t2)
      mm tm (b1, KindedType t1 _ _) t2 = mm tm (b1, t1) t2
      mm tm (b1, t1@(TypeName i1 k1 v1)) (b2, t2@(TypeName i2 k2 v2)) =
	if relatedTypeIds tm i1 i2
	   then return eps
	else if v1 > 0 && b1 then return $ 
	        Map.single (TypeArg i1 k1 Other []) t2
		else if v2 > 0 && b2 then return $
		     Map.single (TypeArg i2 k2 Other []) t1
			else uniResult "typename" i1 
				    "is not unifiable with typename" i2
      mm tm (b1, TypeName i1 k1 v1) (_, t2) =
	if v1 > 0 && b1 then 
	   if occursIn tm i1 t2 then 
	      uniResult "var" i1 "occurs in" t2
	   else return $
			Map.single (TypeArg i1 k1 Other []) t2
	else uniResult "typename" i1  
			    "is not unifiable with type" t2
      mm tm t2 t1@(_, TypeName _ _ _) = mm tm t1 t2
      mm tm (b1, TypeAppl t1 t2) (b2, TypeAppl t3 t4) = 
	match tm (b1, (t1, t2)) (b2, (t3, t4))
      mm tm (b1, ProductType p1 _) (b2, ProductType p2 _) = 
	match tm (b1, p1) (b2, p2)
      mm tm (b1, FunType t1 _ t2 _) (b2, FunType t3 _ t4 _) = 
	match tm (b1, (t1, t2)) (b2, (t3, t4))
      mm _ (_,t1) (_,t2) = uniResult "type" t1  
			    "is not unifiable with type" t2

showPrettyWithPos :: (PrettyPrint a, PosItem a) => a -> ShowS
showPrettyWithPos a =  let p = getMyPos a in
	showChar '\'' . showPretty a . showChar '\'' 
           . noShow (nullPos == p) (showChar ' ' . 
				     showParen True (showPos p))

uniResult :: (PrettyPrint a, PosItem a, PrettyPrint b, PosItem b) =>
	      String -> a -> String -> b -> Result Subst
uniResult s1 a s2 b = 
      Result [Diag Hint ("in type\n" ++ "  " ++ s1 ++ " " ++
			 showPrettyWithPos a "\n  " ++ s2 ++ " " ++
			 showPrettyWithPos b "") nullPos] Nothing

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where  
    subst s (t1, t2) = (subst s t1, subst s t2)
    match tm (b1, (t1, t2)) (b2, (t3, t4)) =
	let r1@(Result _ m1) = match tm (b1, t1) (b2, t3) in
	   case m1 of
	       Nothing -> r1
	       Just s1 -> let r2@(Result _ m2) =
				 match tm (b1, if b1 then subst s1 t2 else t2) 
					  (b2, if b2 then subst s1 t4 else t4)
			      in case m2 of 
				     Nothing -> r2
				     Just s2 -> return $ compSubst s1 s2

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable [a] where
    subst s = map (subst s) 
    match _ (_, []) (_, []) = return eps
    match tm (b1, a1:r1) (b2, a2:r2) = match tm (b1, (a1, r1)) (b2, (a2, r2))
    match tm (b1, []) l = match tm l (b1, [])
    match _ (_, (a:_)) (_, []) = uniResult "type component" a 
		       "is not unifiable with the empty list" 
		       (mkSimpleId "[]")


instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable (Maybe a) where
    subst s = fmap (subst s) 
    match _ (_, Nothing) _ = return eps
    match _ _ (_, Nothing) = return eps
    match tm (b1, Just a1) (b2, Just a2) = match tm (b1, a1) (b2, a2)

unalias :: TypeMap -> Type -> Type
unalias tm = fst . expandAlias tm

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
		     (l, [], unalias tm ts, True)
	    Just (TypeInfo _ _ _
		  (Supertype _ (TypeScheme l (_ :=> ts) _) _)) ->
		     (l, [], unalias tm ts, True)
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

-- | super type ids
superIds :: TypeMap -> Id -> Set.Set Id
superIds tm = supIds tm Set.empty . Set.single

subIds :: TypeMap -> Id -> Set.Set Id
subIds tm i = foldr ( \ j s ->
		 if Set.member i $ superIds tm j then
		      Set.insert j s else s) Set.empty $ Map.keys tm

supIds :: TypeMap -> Set.Set Id -> Set.Set Id -> Set.Set Id
supIds tm known new = 
    if Set.isEmpty new then known else 
       let more = Set.unions $ map superTypeToId $ 
		  concatMap ( \ i -> superTypes 
			    $ Map.findWithDefault starTypeInfo i tm)
                  $ Set.toList new 
	   newKnown = Set.union known new
    in supIds tm newKnown (more Set.\\ newKnown)

starTypeInfo :: TypeInfo
starTypeInfo = TypeInfo star [] [] NoTypeDefn

superTypeToId :: Type -> Set.Set Id
superTypeToId t = 
    case t of
	   TypeName i _ _ -> Set.single i
	   _ -> Set.empty
