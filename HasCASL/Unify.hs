{- > HetCATS/HasCASL/Unify.hs
   > $Id$
   > Authors: Christian Maeder
   > Year:    2003
   
   substitution and unification of types
-}

module HasCASL.Unify where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs
import Common.PrettyPrint
import Common.Id
import HasCASL.Le
import Common.Lib.State
import qualified Common.Lib.Map as Map
import Common.Result
import Data.List
import Data.Maybe

unifiable :: TypeScheme -> TypeScheme -> State Env Bool
unifiable sc1 sc2 =
    do tm <- gets typeMap
       c <- gets counter
       let Result ds mm = evalState (unifIable tm sc1 sc2) c
       appendDiags ds
       return $ isJust mm

isUnifiable :: TypeMap -> Int -> TypeScheme -> TypeScheme -> Bool
isUnifiable tm c sc1 sc2 = isJust $ maybeResult $ 
			   evalState (unifIable tm sc1 sc2) c

unifIable :: TypeMap -> TypeScheme -> TypeScheme -> State Int (Result Subst)
unifIable tm sc1 sc2 =
    do t1 <- freshInst sc1
       t2 <- freshInst sc2
       return $ unify tm t1 t2

freshInst :: TypeScheme -> State Int Type
freshInst (TypeScheme tArgs (_ :=> t) _) = 
    do m <- mkSubst tArgs 
       return $ subst m t

freshVar :: State Int Id 
freshVar = 
    do c <- get
       put (c + 1)
       return $ simpleIdToId $ mkSimpleId ("_var_" ++ show c)

freshType :: Kind -> State Int Type
freshType k = 
    do tId <- freshVar
       return $ TypeName tId k 1

mkSingleSubst :: TypeArg -> State Int Subst
mkSingleSubst tv@(TypeArg _ k _ _) =
    do ty <- freshType k
       return $ Map.single tv ty

mkSubst :: [TypeArg] -> State Int Subst
mkSubst tas = do ms <- mapM mkSingleSubst tas
		 return $ Map.unions ms
 		   
type Subst = Map.Map TypeArg Type

instance Ord TypeArg where
    TypeArg v1 k1 _ _ <= TypeArg v2 k2 _ _
	= (v1, k1) <= (v2, k2)

instance Ord Kind where
-- only for expanded kinds
    KindAppl k1 k2 _ <= KindAppl k3 k4 _ = (k1, k2) <= (k3, k4)
    KindAppl _ _ _ <= ExtClass _ _ _ = False
    ExtClass _ _ _ <= _ = True 

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
    unify tm t1@(TypeName i1 k1 v1) t2@(TypeName i2 k2 v2) =
	if i1 == i2 then return $ Map.empty
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
    unify tm t1@(TypeName i1 k1 v1) t2@(TypeAppl _ _) =
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
    unify tm t2@(TypeAppl _ _) t1@(TypeName _ _ _) = unify tm t1 t2
    unify tm t12@(TypeAppl t1 t2) t34@(TypeAppl t3 t4) = 
	let (ta, a) = expandAlias tm t12
	    (tb, b) = expandAlias tm t34 in
	   if a || b then unify tm ta tb
	      else unify tm (t1, t2) (t3, t4)
    unify tm (ProductType p1 _) (ProductType p2 _) = unify tm p1 p2
    unify tm (FunType t1 _ t2 _) (FunType t3 _ t4 _) = 
	unify tm (t1, t2) (t3, t4)
    unify tm t1 (LazyType t2 _) = unify tm t1 t2
    unify tm (LazyType t1 _) t2 = unify tm t1 t2
    unify tm t1 (KindedType t2 _ _) = unify tm t1 t2
    unify tm (KindedType t1 _ _) t2 = unify tm t1 t2
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
				     Just s2 -> return $
						(Map.map (subst s2) s1 
						   `Map.union` s2) 

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable [a] where
    subst s = map (subst s) 
    unify _ [] [] = return $ Map.empty
    unify tm (a1:r1) (a2:r2) = unify tm (a1, r1) (a2, r2)
    unify tm [] l = unify tm l [] 
    unify _ (a:_) [] = Result [mkDiag Hint 
			 ("unification failed at") a] Nothing

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
	  else (t, False)

expandAliases :: TypeMap -> Type -> ([TypeArg], [Type], Type, Bool)
expandAliases tm t@(TypeName i _ _) =
       case Map.lookup i tm of 
            Just (TypeInfo _ _ _ 
		  (AliasTypeDefn (TypeScheme l (_ :=> ts) _))) ->
				     (l, [], ts, True)
	    _ -> ([], [], t, False)

expandAliases tm t@(TypeAppl t1 t2) =
    let (ps, as, ta, b) = expandAliases tm t1 in
       if b then 
	  (ps, t2:as, ta, b)  -- reverse later on
	  else ([], [], t, False)

expandAliases _ t = ([], [], t, False)
