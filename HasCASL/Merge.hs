
{- HetCATS/HasCASL/Merge.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002/2003
   
   merging (parts of) local env
-}

module HasCASL.Merge where

import Common.Id
import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.Unify
import qualified Common.Lib.Map as Map
import Data.List
import Control.Monad.State
import Common.Result

-- for Logic.signature_union

class Mergeable a where
    merge :: a -> a -> Result a 

instance Mergeable Env where
    merge e1 e2 =
	do cMap <- merge (classMap e1) $ classMap e2
	   tMap <- merge (typeMap e1) $ typeMap e2
	   let m = max (counter e1) $ counter e2
	   as <- mergeAssumps tMap m 
		 (assumps e1) $ assumps e2
	   return $ Env cMap tMap as (envDiags e1 ++ envDiags e2) m

instance (Ord a, PosItem a, Mergeable b) => Mergeable (Map.Map a b) where
    merge = mergeMap merge

mergeMap :: (Ord a, PosItem a) => (b -> b -> Result b) 
	 -> Map.Map a b -> Map.Map a b -> Result  (Map.Map a b)
mergeMap f m1 m2 = foldM ( \ m (k, v) -> 
			  case k `Map.lookup` m of
			  Nothing -> return $ Map.insert k v m
			  Just w -> 
			      let Result ds mu = f v w
			          ns = map ( \ d -> if diagPos d == nullPos 
					     then d { diagPos = posOf [k] } 
					     else d) ds 
			      in case mu of 
			         Nothing -> Result ns $ Nothing
			         Just u -> return $ Map.insert k u m)
		  m1 (Map.toList m2)  

instance Mergeable a => Mergeable (Maybe a) where
    merge m1 m2 = case m1 of 
			  Nothing -> return m2
			  Just v1 -> case m2 of 
					     Nothing -> return m1
					     Just v2 -> do v <- merge v1 v2
							   return $ Just v

instance Mergeable ClassInfo where
    merge c1 c2 = do k <- merge (classKind c1) (classKind c2)
		     d <- merge (classDefn c1) (classDefn c2)
		     let s1 = superClasses c1
			 s2 = superClasses c2
		     if s1 == s2 then 
			return $ ClassInfo s1 k d 
			else fail "merge: non-equal super classes"

instance Mergeable Kind where
    merge k1 k2 = if k1 == k2 then return k1
		  else fail "merge: non-equal kinds"

instance Mergeable Class where
    merge c1@(Downset t1) (Downset t2) =
	if t1 == t2 then return c1
	   else fail "merge: non-equal downset"
    merge c1@(Intersection i1 _) (Intersection i2 _) =
       if i1 == i2 then return c1
	  else fail "merge: non-equal intersection class" 
    merge _ _ = fail "merge: class"

mergeList :: Eq a => [a] -> [a] -> Result [a]
mergeList l1 l2 = return $ nub (l1 ++ l2)

instance Mergeable TypeInfo where
    merge t1 t2 = do k <- merge (typeKind t1) $ typeKind t2
		     o <- mergeList (otherTypeKinds t1) $ otherTypeKinds t2
		     s <- mergeList (superTypes t1) $ superTypes t2
	             d <- merge (typeDefn t1) $ typeDefn t2
		     return $ TypeInfo k o s d 

instance Mergeable TypeDefn where
    merge d1 d2 = 
	case (d1, d2) of 
	    (TypeVarDefn, TypeVarDefn) -> return d1
	    (TypeVarDefn, _) -> fail "merge: TypeVarDefn"
	    (_, TypeVarDefn) -> fail "merge: TypeVarDefn"
	    (NoTypeDefn, AliasTypeDefn _) -> fail "merge: AliasTypeDefn" 
	    (AliasTypeDefn _, NoTypeDefn) -> fail "merge: AliasTypeDefn"
	    (NoTypeDefn, _) -> return d2
	    (_, NoTypeDefn) -> return d1
	    (_, _) -> if d1 == d2 then return d1 else
		      fail "merge: TypeDefn"

mergeAssumps :: TypeMap -> Int -> Assumps -> Assumps -> Result Assumps
mergeAssumps tm c = mergeMap (mergeOpInfos tm c)

mergeOpInfos :: TypeMap -> Int -> [OpInfo] -> [OpInfo] -> Result [OpInfo] 
mergeOpInfos tm c l1 l2 = 
    foldM ( \ l o -> 
	   let os = opType o
	       (es, us) = partition (\ e -> opType e == os) l
	   in if null es then 
	       let bs = map (isUnifiable tm c os . opType) l
	       in if or bs then fail "illegal overloading" 
	          else return (o:l)
	      else do r <- merge o $ head es
	              return (r : us)) l1 l2 


instance Mergeable OpInfo where
    merge o1 o2 = 
	do sc <- merge (opType o1) $ opType o2
           as <- merge (opAttrs o1) $ opAttrs o2
 	   d <- merge (opDefn o1) $ opDefn o2
	   return $ OpInfo sc as d

instance Mergeable TypeScheme where
    merge s1 s2 = if s1 == s2 then return s1 
		  else fail "unequal type schemes" 

instance Mergeable [OpAttr] where
    merge l1 l2 = 
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
	if t1 == t2 then return $ UnitOpAttr t1 (p1 ++ p2)
	   else fail "unequal unit elements"
    merge _ _ = fail "merge: OpAttr"

instance Mergeable OpDefn where
    merge VarDefn VarDefn = return VarDefn
    merge VarDefn _       = fail "merge: VarDefn"
    merge _ VarDefn       = fail "merge: VarDefn"
    merge NoOpDefn d      = return d
    merge d NoOpDefn      = return d
    merge d@(ConstructData d1) (ConstructData d2) = 
	if d1 == d2 then return d else 
	   fail "merge: constructor"
    merge d@(SelectData c1 d1) (SelectData c2 d2) = 
	if d1 == d2 && sort c1 == sort c2 then return d else 
	   fail "merge: selector"
    merge d@(Definition d1) (Definition d2) =  
	if d1 == d2 then return d else 
	   fail "merge: definition"
    merge _ _ = fail "merge: OpDefn"

	    

