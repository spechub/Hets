{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   merging parts of local environment
-}

module HasCASL.Merge where

import Common.Id
import Common.PrettyPrint
import Common.Result

import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.PrintLe
import HasCASL.Unify
import HasCASL.MapTerm
import qualified Common.Lib.Map as Map

import Control.Monad(foldM)



instance (Ord a, PosItem a, PrettyPrint a, Mergeable b) 
    => Mergeable (Map.Map a b) where
    merge = mergeMap id merge

improveDiag :: (PosItem a, PrettyPrint a) => a -> Diagnosis -> Diagnosis
improveDiag v d = d { diagString = let f:l = lines $ diagString d in 
		      unlines $ (f ++ " of '" ++ showPretty v "'") : l
		    , diagPos = getMyPos v
		    , diagKind = case diagKind d of 
		                 FatalError -> Error
		                 w -> w 
		    }

mergeMap :: (Ord a, PosItem a, PrettyPrint a) => 
	    (b -> b) -> (b -> b -> Result b) 
	 -> Map.Map a b -> Map.Map a b -> Result  (Map.Map a b)
mergeMap e f m1 m2 = foldM ( \ m (k, v) -> 
			  case k `Map.lookup` m of
			  Nothing -> return $ Map.insert k (e v) m
			  Just w -> 
			      let Result ds mu = f (e v) w
			          ns = map (improveDiag k) ds  
			      in case mu of 
			         Nothing -> Result ns $ Nothing
			         Just u -> Result ns $ Just $ Map.insert k u m)
		  Map.empty (Map.toList m1 ++ Map.toList m2)  

instance Mergeable a => Mergeable (Maybe a) where
    merge m1 m2 = case m1 of 
			  Nothing -> return m2
			  Just v1 -> case m2 of 
					     Nothing -> return m1
					     Just v2 -> do v <- merge v1 v2
							   return $ Just v

instance Mergeable ClassInfo where
    merge = mergeA "super classes"

instance Mergeable Kind where
    merge = mergeA "super kinds" 

mergeTypeInfo :: TypeInfo -> TypeInfo -> Result TypeInfo 
mergeTypeInfo t1 t2 = 
    do k <- merge (typeKind t1) $ typeKind t2
       o <- merge (otherTypeKinds t1) $ otherTypeKinds t2
       s <- merge (superTypes t1) $ superTypes t2
       d <- mergeTypeDefn (typeDefn t1) $ typeDefn t2
       return $ TypeInfo k o s d 

mergeTypeDefn :: TypeDefn -> TypeDefn -> Result TypeDefn
mergeTypeDefn d1 d2 = 
	case (d1, d2) of 
	    (TypeVarDefn 0, TypeVarDefn _) -> return d2
	    (TypeVarDefn _, TypeVarDefn 0) -> return d1
	    (TypeVarDefn c1, TypeVarDefn c2) -> do 
	        c <- mergeA "TypeVarDefn" c1 c2
		return $ TypeVarDefn c
	    (TypeVarDefn _, _) -> fail "merge: TypeVarDefn"
	    (_, TypeVarDefn _) -> fail "merge: TypeVarDefn"
	    (_, DatatypeDefn _) -> return d2 
	    (PreDatatype, _) -> fail "expected data type definition"
	    (_, PreDatatype) -> return d1
	    (NoTypeDefn, _) -> return d2
	    (_, NoTypeDefn) -> return d1
	    (AliasTypeDefn s1, AliasTypeDefn s2) -> 
		do s <- mergeScheme s1 s2
		   return $ AliasTypeDefn s
	    (Supertype v1 s1 t1, Supertype v2 s2 t2) -> 
		do s <- mergeScheme s1 s2
		   v <- merge v1 v2
		   t <- mergeTerm t1 t2
		   return $ Supertype v s t
	    (_, _) -> mergeA "TypeDefn" d1 d2

instance Mergeable Vars where
    merge = mergeA "variables for subtype definition"

mergeScheme :: TypeScheme -> TypeScheme -> Result TypeScheme
mergeScheme s1@(TypeScheme a1 t1 _)
	    s2@(TypeScheme a2 t2 _) = 
    let v1 = genVarsOf t1
	v2 = genVarsOf t2
	mp v = mapArg $ zip v [(1::Int)..] 
    in 
    if t1 == t2 then 
       if null a1 && null a2 || isSingle a1 && isSingle a2 then 
	  return s1
       else if map (mp v1) a1 == map (mp v2) a2 then return s1
		else fail ("differently bound type variables" 
			 ++ expected s1 s2) 
    else fail ("wrong type scheme" ++ expected s1 s2)

instance Mergeable OpInfo where
   merge o1 o2 = 
	do sc <- mergeScheme (opType o1) $ opType o2
           as <- merge (opAttrs o1) $ opAttrs o2
 	   d <- merge (opDefn o1) $ opDefn o2
	   return $ OpInfo sc as d

instance Mergeable OpAttr where
    merge (UnitOpAttr t1 p1) (UnitOpAttr t2 p2) = 
	do t <- mergeTerm t1 t2
	   return $ UnitOpAttr t (p1 ++ p2)
    merge a1 a2 = mergeA "attributes" a1 a2 

instance Mergeable OpBrand where
    merge Pred _ = return Pred
    merge _ Pred = return Pred
    merge Op _   = return Op
    merge _ Op   = return Op
    merge _ _    = return Fun
    
instance Mergeable OpDefn where
    merge VarDefn VarDefn = return VarDefn
    merge VarDefn _       = fail "illegal redeclaration of a variable"
    merge _ VarDefn       = fail "illegal redeclaration as variable"
    merge (NoOpDefn _) d  = return d
    merge d (NoOpDefn _)  = return d
    merge (ConstructData d1) (ConstructData d2) = do 
        d <- mergeA "constructor target type" d1 d2
	return $ ConstructData d
    merge (SelectData c1 d1) (SelectData c2 d2) = do
        d <- mergeA "selector source type" d1 d2
	c <- merge c1 c2
	return $ SelectData c d
    merge (Definition b1 d1) (Definition b2 d2) =
	do d <- mergeTerm d1 d2
	   b <- merge b1 b2
	   return $ Definition b d
    merge _d1 _d2 = fail "illegal redefinition"

instance Eq a => Mergeable [a] where
    merge [] l2 = return l2
    merge (e:l1) l2 = do 
      l3 <- merge l1 l2
      return $ if any (e==) l2 then l3
	 else e:l3

mergeOpInfos :: OpInfos -> OpInfos -> Result OpInfos 
mergeOpInfos (OpInfos l1) (OpInfos l2) = 
    do l <- merge l1 l2
       return $ OpInfos  l

instance Mergeable Env where
    merge e1 e2 =
	do cMap <- merge (classMap e1) $ classMap e2
	   tMap <- mergeMap id mergeTypeInfo
		   (typeMap e1) $ typeMap e2
	   as <- mergeMap (OpInfos . 
			   map (mapOpInfo (id, expandAlias tMap)) . opInfos) 
		 mergeOpInfos
		 (assumps e1) $ assumps e2
	   return initialEnv { classMap = cMap
			     , typeMap = tMap
			     , assumps = as }

mergeA :: (PrettyPrint a, Eq a) => String -> a -> a -> Result a
mergeA str t1 t2 = if t1 == t2 then return t1 else 
    fail ("different " ++ str ++ expected t1 t2)

mergeTerm :: (PrettyPrint a, Eq a) => a -> a -> Result a
mergeTerm = mergeA "terms"
