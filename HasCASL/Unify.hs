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
import Data.List as List
import Data.Maybe

-- | check for unbound type variables
unboundTypevars :: [TypeArg] -> Type -> [Diagnosis]
unboundTypevars args ct = 
    let restVars = varsOf ct List.\\ args in
    if null restVars then []
       else [mkDiag Error ("unbound type variable(s)\n\t"
				  ++ showSepList ("," ++) showPretty 
				  restVars " in") ct]

-- | vars
varsOf :: Type -> [TypeArg]
varsOf = leaves (/=0)

-- | bound vars
genVarsOf :: Type -> [TypeArg]
genVarsOf = leaves (<0)

-- | vars or other ids 
leaves :: (Int -> Bool) -> Type -> [TypeArg]
leaves b t = 
    case t of 
	   TypeName j k i -> if b(i)
			     then [TypeArg j k Other []]
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
    do (t1, _) <- freshInstList sc1
       (t2, _) <- freshInstList sc2
       return $ f t1 t2

asSchemes :: Int -> (Type -> Type -> a) -> TypeScheme -> TypeScheme -> a
asSchemes c f sc1 sc2 = fst $ runState (toSchemes f sc1 sc2) c

-- -------------------------------------------------------------------------
freshInstList :: TypeScheme -> State Int (Type, [Type])
freshInstList (TypeScheme tArgs t _) = 
    do let vs = genVarsOf t
       ts <- mkSubst vs  
       return (rename ( \ i k n -> if n < 0 then 
			ts !! (-1-n) else TypeName i k n) t, 
	       map (mapArg $ zip vs ts) tArgs)

mapArg :: [(TypeArg, a)] -> TypeArg -> a
mapArg ts (TypeArg i k _ _) = 
    maybe (error "mapArg") snd $ 
            find (\ (TypeArg j l _ _, _) -> i == j && k == l) ts

freshVar :: Pos -> State Int (Id, Int) 
freshVar p = 
    do c <- get
       put (c + 1)
       return (simpleIdToId $ Token ("_var_" ++ show c) p, c)

mkSingleSubst :: TypeArg -> State Int Type
mkSingleSubst tv@(TypeArg _ k _ _) =
    do (ty, c) <- freshVar $ posOfTypeArg tv
       return (TypeName ty k c)

mkSubst :: [TypeArg] -> State Int [Type]
mkSubst = mapM mkSingleSubst
 		   
type Subst = Map.Map Int Type

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
idsOf b = Set.fromList . map getTypeVar . leaves b

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
	   TypeAppl t1 t2 -> TypeAppl (rename m t1) (rename m t2)
	   ExpandedType t1 t2 -> ExpandedType (rename m t1) (rename m t2)
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
	       case Map.lookup n m of
	       Just s -> s
	       _ -> TypeName i k n)
    match = mm where 
      mm tm t1 (b2, ExpandedType _ t2) = mm tm t1 (b2, t2)
      mm tm (b1, ExpandedType _ t1) t2 = mm tm (b1, t1) t2
      mm tm t1 (b2, LazyType t2 _) = mm tm t1 (b2, t2)
      mm tm (b1, LazyType t1 _) t2 = mm tm (b1, t1) t2
      mm tm t1 (b2, KindedType t2 _ _) = mm tm t1 (b2, t2)
      mm tm (b1, KindedType t1 _ _) t2 = mm tm (b1, t1) t2
      mm tm (b1, t1@(TypeName i1 _ v1)) (b2, t2@(TypeName i2 _ v2)) =
        if relatedTypeIds tm i1 i2
           then return eps
        else if v1 > 0 && b1 then return $ 
                Map.single v1 t2
                else if v2 > 0 && b2 then return $
                     Map.single v2 t1
                        else uniResult "typename" i1 
                                    "is not unifiable with typename" i2
      mm tm (b1, TypeName i1 _ v1) (_, t2) =
        if v1 > 0 && b1 then 
           if occursIn tm i1 t2 then 
              uniResult "var" i1 "occurs in" t2
           else return $
                        Map.single v1 t2
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

repl :: Map.Map TypeArg Type -> Type -> Type
repl m = rename ( \ i k n -> 
		 case Map.lookup (TypeArg i k Other []) m of
		      Just s -> s 
		      Nothing -> TypeName i k n)

expand :: TypeMap -> TypeScheme -> TypeScheme
expand = mapTypeOfScheme . expandAlias  

expandAlias :: TypeMap -> Type -> Type
expandAlias tm t = 
    let (ps, as, ta, b) = expandAliases tm t in
       if b && length ps == length as then
	  ExpandedType t $ repl (Map.fromList (zip ps $ reverse as)) ta
	  else ta

expandAliases :: TypeMap -> Type -> ([TypeArg], [Type], Type, Bool)
expandAliases tm t = case t of 
    TypeName i _ _ -> case Map.lookup i tm of 
            Just (TypeInfo _ _ _ 
		  (AliasTypeDefn (TypeScheme l ty _))) ->
		     (l, [], ty, True)
	    Just (TypeInfo _ _ _
		  (Supertype _ (TypeScheme l ty _) _)) ->
		     (l, [], ty, True)
	    _ -> wrap t
    TypeAppl t1 t2 -> 
	let (ps, as, ta, b) = expandAliases tm t1 
	    t3 = expandAlias tm t2
	in if b then 
	  (ps, t3:as, ta, b)  -- reverse later on
	  else wrap $ TypeAppl t1 t3
    FunType t1 a t2 ps -> 
	wrap $ FunType (expandAlias tm t1) a (expandAlias tm t2) ps
    ProductType ts ps -> wrap $ ProductType (map (expandAlias tm) ts) ps
    LazyType ty ps -> wrap $ LazyType (expandAlias tm ty) ps
    ExpandedType t1 t2 -> wrap $ ExpandedType t1 $ expandAlias tm t2
    KindedType ty k ps -> wrap $ KindedType (expandAlias tm ty) k ps
    _ -> wrap t
    where wrap ty = ([], [], ty, False)

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
