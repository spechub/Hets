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
import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.Unify
import qualified Common.Lib.Map as Map
import Data.List
import Control.Monad
import Common.Result

-- for Logic.signature_union

instance (Ord a, PosItem a, PrettyPrint a, Mergeable b) 
    => Mergeable (Map.Map a b) where
    merge = mergeMap merge

improveDiag :: (PosItem a, PrettyPrint a) => a -> Diagnosis -> Diagnosis
improveDiag v d = d { diagString = let f:l = lines $ diagString d in 
		      unlines $ (f ++ " of '" ++ showPretty v "'") : l
		    , diagPos = getMyPos v
		    , diagKind = case diagKind d of 
		                 FatalError -> Error
		                 w -> w 
		    }

mergeMap :: (Ord a, PosItem a, PrettyPrint a) => (b -> b -> Result b) 
	 -> Map.Map a b -> Map.Map a b -> Result  (Map.Map a b)
mergeMap f m1 m2 = foldM ( \ m (k, v) -> 
			  case k `Map.lookup` m of
			  Nothing -> return $ Map.insert k v m
			  Just w -> 
			      let Result ds mu = f v w
			          ns = map (improveDiag k) ds  
			      in case mu of 
			         Nothing -> Result ns $ Nothing
			         Just u -> Result ns $ Just $ Map.insert k u m)
		  m1 (Map.toList m2)  

instance Mergeable a => Mergeable (Maybe a) where
    merge m1 m2 = case m1 of 
			  Nothing -> return m2
			  Just v1 -> case m2 of 
					     Nothing -> return m1
					     Just v2 -> do v <- merge v1 v2
							   return $ Just v

instance Mergeable ClassInfo where
    merge c1 c2 = if c1 == c2 then 
			return c1
			else fail "merge: non-equal super classes"

instance Mergeable Kind where
    merge k1 k2 = if k1 == k2 then return k1
		  else fail "merge: non-equal kinds"

mergeList :: Eq a => [a] -> [a] -> Result [a]
mergeList l1 l2 = return $ nub (l1 ++ l2)

mergeTypeInfo :: TypeMap -> Int -> TypeInfo -> TypeInfo -> Result TypeInfo 
mergeTypeInfo tm c t1 t2 = 
    do k <- merge (typeKind t1) $ typeKind t2
       o <- mergeList (otherTypeKinds t1) $ otherTypeKinds t2
       s <- mergeList (superTypes t1) $ superTypes t2
       d <- mergeTypeDefn tm c (typeDefn t1) $ typeDefn t2
       return $ TypeInfo k o s d 


mergeTypeDefn :: TypeMap -> Int -> TypeDefn -> TypeDefn -> Result TypeDefn
mergeTypeDefn tm c d1 d2 = 
	case (d1, d2) of 
	    (TypeVarDefn, TypeVarDefn) -> return d1
	    (TypeVarDefn, _) -> fail "merge: TypeVarDefn"
	    (_, TypeVarDefn) -> fail "merge: TypeVarDefn"
	    (PreDatatype, DatatypeDefn _ _ _) -> return d2 
	    (PreDatatype, _) -> fail "expected data type definition"
	    (_, PreDatatype) -> return d1
--	    (NoTypeDefn, AliasTypeDefn _) -> fail "merge: AliasTypeDefn" 
--	    (AliasTypeDefn _, NoTypeDefn) -> fail "merge: AliasTypeDefn"
	    (NoTypeDefn, _) -> return d2
	    (_, NoTypeDefn) -> return d1
	    (AliasTypeDefn s1, AliasTypeDefn s2) -> 
		do s <- mergeScheme tm c s1 s2
		   return $ AliasTypeDefn s
	    (Supertype v1 s1 t1, Supertype v2 s2 t2) -> 
		do s <- mergeScheme tm c s1 s2
		   v <- merge v1 v2
		   t <- merge t1 t2
		   return $ Supertype v s t
	    (_, _) -> if d1 == d2 then return d1 else
		      fail "merge: TypeDefn"

instance Mergeable Vars where
    merge t1 t2 = if t1 == t2 then return t1 
		  else fail ("different variables for subtype definition\n\t" 
			     ++ showPretty t1 "\n\t"
			     ++ showPretty t2 "\n\t")

mergeOpInfos :: TypeMap -> Int -> OpInfos -> OpInfos -> Result OpInfos 
mergeOpInfos tm c (OpInfos l1) (OpInfos l2) = fmap OpInfos $  
    foldM ( \ l o -> 
	   let (es, us) = partition (isUnifiable tm c (opType o) . opType) l
	   in if null es then return (o:l)
	      else do r <- mergeOpInfo tm c (head es) o
	              return (r : us)) l1 l2 

mergeScheme :: TypeMap -> Int -> TypeScheme -> TypeScheme -> Result TypeScheme
mergeScheme tm c s1 s2 = let b = instScheme tm c s2 s1 in
    if instScheme tm c s1 s2 then 
       if b then return s1 
	  else fail ("found scheme is only a subsitution instance" 
		     ++ expected s1 s2)
       else if b then 
	    fail ("expected scheme is only a subsitution instance" 
		     ++ expected s1 s2)
	    else fail ("wrong type scheme" ++ expected s1 s2)  

mergeOpInfo :: TypeMap -> Int -> OpInfo -> OpInfo -> Result OpInfo
mergeOpInfo tm c o1 o2 = 
	do sc <- mergeScheme tm c (opType o1) $ opType o2
           as <- mergeAttrs (opAttrs o1) $ opAttrs o2
 	   d <- merge (opDefn o1) $ opDefn o2
	   return $ OpInfo sc as d

-- instance Mergeable [OpAttr] where
mergeAttrs :: [OpAttr] -> [OpAttr] -> Result [OpAttr]
mergeAttrs l1 l2 = 
	let binAttr a = case a of BinOpAttr _ _ -> True
				  _ -> False
	    (l1b, l1u) = partition binAttr l1
	    (l2b, l2u) = partition binAttr l2
	    lb = nubBy ( \ (BinOpAttr b1 _) (BinOpAttr b2 _) -> b1 == b2) 
		 (l1b ++ l2b)
        in if null l1u || null l2u then 
	   return (l1u ++ l2u ++ lb)
	   else do u <- merge (head l1u) (head l2u) 
		   return (u : lb) 

instance Mergeable OpAttr where
    merge (UnitOpAttr t1 p1) (UnitOpAttr t2 p2) = 
	do t <- merge t1 t2
	   return $ UnitOpAttr t1 (p1 ++ p2)
    merge _ _ = fail "merge: OpAttr"

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
    merge d@(ConstructData d1) (ConstructData d2) = 
	if d1 == d2 then return d else 
	   fail ("wrong constructor target type" ++
		 expected d1 d2)
    merge (SelectData c1 d1) (SelectData c2 d2) = 
	if d1 == d2 then
	   do c <- mergeConstrInfos c1 c2
	      return $ SelectData c d1
	else fail ("wrong selector's source type" ++
		   expected d1 d2)
    merge (Definition b1 d1) (Definition b2 d2) =
	do d <- merge d1 d2
	   b <- merge b1 b2
	   return $ Definition b d
    merge _d1 _d2 = fail "illegal redefinition"

mergeConstrInfos :: [ConstrInfo] -> [ConstrInfo] -> Result [ConstrInfo]
mergeConstrInfos [] c2 = return c2
mergeConstrInfos (c : r) c2 =
    do c3 <- mergeConstrInfos r c2
       let cs = filter (==c) c2
       if null cs then 
	   return (c : c3)
	   else return c3

instance Mergeable Term where
    merge t1 t2 = if t1 == t2 then return t1 
		  else fail ("different terms\n\t" 
			     ++ showPretty t1 "\n\t"
			     ++ showPretty t2 "\n\t")

