{- > HetCATS/HasCASL/Unify.hs
   > $Id$
   > Authors: Christian Maeder
   > Year:    2003
   
   substitution and unification of types
-}

module HasCASL.Unify where

import HasCASL.As
import HasCASL.PrintAs
import HasCASL.ClassAna
import Common.PrettyPrint
import Common.Id
import HasCASL.Le
import Control.Monad.State
import qualified Common.Lib.Map as Map
import Common.Result
import Data.List
import Data.Maybe

unifiable :: TypeScheme -> TypeScheme -> State Env Bool
unifiable sc1 sc2 =
    do t1 <- freshInst sc1
       t2 <- freshInst sc2
       Result ds mm <- unify t1 t2
       appendDiags ds
       return $ isJust mm

freshInst :: TypeScheme -> State Env Type
freshInst (TypeScheme tArgs (_ :=> t) _) = 
    do c <- getCounter
       putCounter (c + length tArgs)
       return $ subst (mkSubst tArgs c) t

type Subst = Map.Map TypeArg Type

instance Ord TypeArg where
    TypeArg v1 k1 _ _ <= TypeArg v2 k2 _ _
	= (v1, k1) <= (v2, k2)

instance Ord Kind where
-- only for expanded kinds
    ExtClass _ _ _ <= KindAppl _ _ _ = True 
    ExtClass _ _ _ <= ExtClass _ _ _ = True 
    KindAppl _ _ _ <= ExtClass _ _ _ = False
    KindAppl k1 k2 _ <= KindAppl k3 k4 _ = (k1, k2) <= (k3, k4)

mkSubst :: [TypeArg] -> Int -> Subst
mkSubst [] _ = Map.empty
mkSubst (tv@(TypeArg _ k _ _):r) i =
     let tId = simpleIdToId $ mkSimpleId ("_var_" ++ show i)
     in Map.insert tv (TypeName tId k 1) $ mkSubst r (i+1) 
 		   
class Unifiable a where
    subst :: Subst -> a -> a
    unify :: a -> a -> State Env (Result Subst)

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
    unify t1@(TypeName i1 k1 v1) t2@(TypeName i2 k2 v2) =
	if i1 == i2 then return $ return $ Map.empty
	else if v1 > 0 then return $ return $ 
	        Map.single (TypeArg i1 k1 Other []) t2
		else if v2 > 0 then return $ return $
		     Map.single (TypeArg i2 k2 Other []) t1
			else 
		 do (a1, b1) <- expandAlias t1 
		    (a2, b2) <- expandAlias t2
		    if b1 || b2 then unify a1 a2
		       else return $ Result [mkDiag Hint 
					("type '" ++ showId i1 
					 "' is not unifiable with") i2]
					Nothing
    unify t1@(TypeName i1 k1 v1) t2@(TypeAppl _ _) =
	if v1 > 0 then 
	   if i1 `occursIn` t2 then 
	      return $ Result [mkDiag Hint 
			       ("var '" ++ showId i1 
				"' occurs in") t2] Nothing
	   else return $ return $
			Map.single (TypeArg i1 k1 Other []) t2
	else do (a1, b1) <- expandAlias t1 
		if b1 then unify a1 t2
		   else return $ Result 
			    [mkDiag Hint 
			     ("type '" ++ showId i1 
			      "' is not unifiable with") t2] Nothing
    unify t2@(TypeAppl _ _) t1@(TypeName _ _ _) = unify t1 t2
    unify t12@(TypeAppl t1 t2) t34@(TypeAppl t3 t4) = 
	do (ta, a) <- expandAlias t12
	   (tb, b) <- expandAlias t34
	   if a || b then unify ta tb
	      else unify (t1, t2) (t3, t4)
    unify (ProductType p1 _) (ProductType p2 _) = unify p1 p2
    unify (FunType t1 _ t2 _) (FunType t3 _ t4 _) = unify (t1, t2) (t3, t4)
    unify t1 (LazyType t2 _) = unify t1 t2
    unify (LazyType t1 _) t2 = unify t1 t2
    unify t1 (KindedType t2 _ _) = unify t1 t2
    unify (KindedType t1 _ _) t2 = unify t1 t2
    unify t1 t2 = return $ Result [mkDiag Hint 
				   ("type '" ++ showPretty t1 
				    "' is not unifiable with") t2] Nothing

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where  
    subst s (t1, t2) = (subst s t1, subst s t2)
    unify (t1, t2) (t3, t4) =
	do r1@(Result _ m1) <- unify t1 t3
	   case m1 of
	       Nothing -> return r1
	       Just s1 -> do r2@(Result _ m2) <- 
				 unify (subst s1 t2) (subst s1 t4) 
			     case m2 of 
				     Nothing -> return r2
				     Just s2 -> return $ return $
						(Map.map (subst s2) s1 
						   `Map.union` s2) 

instance (PrettyPrint a, PosItem a, Unifiable a) => Unifiable [a] where
    subst s = map (subst s) 
    unify [] [] = return $ return $ Map.empty
    unify (a1:r1) (a2:r2) = unify (a1, r1) (a2, r2)
    unify [] l = unify l [] 
    unify (a:_) [] = return $ Result [mkDiag Hint 
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

expandAlias :: Type -> State Env (Type, Bool)
expandAlias t = 
    do (ps, as, ta, b) <- expandAliases t
       if b && length ps == length as then
	  return (subst (Map.fromList (zip ps $ reverse as)) ta, b)
	  else return (t, False)

expandAliases :: Type -> State Env ([TypeArg], [Type], Type, Bool)
expandAliases t@(TypeName i _ _) =
    do tk <- getTypeMap
       case Map.lookup i tk of 
            Just (TypeInfo _ _ _ 
		  (AliasTypeDefn (TypeScheme l (_ :=> ts) _))) ->
				     return (l, [], ts, True)
	    _ -> return ([], [], t, False)

expandAliases t@(TypeAppl t1 t2) =
    do (ps, as, ta, b) <- expandAliases t1 
       if b then 
	  return (ps, t2:as, ta, b)  -- reverse later on
	  else return ([], [], t, False)

expandAliases t = return ([], [], t, False)
