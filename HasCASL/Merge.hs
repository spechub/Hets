
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
	   as <- merge (assumps e1) $ assumps e2
	   return $ Env cMap tMap as (envDiags e1 ++ envDiags e2)
		      (max (counter e1) $ counter e2)

instance (Ord a, PosItem a, Mergeable b) => Mergeable (Map.Map a b) where
    merge m1 m2 = foldM ( \ m (k, v) -> 
			  case k `Map.lookup` m of
			  Nothing -> return $ Map.insert k v m
			  Just w -> 
			      let Result ds mu = merge v w
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
			else fatal_error "merge: non-equal super classes"
			     $ posOfId $ head (s1++s2) 

instance Mergeable Kind where
    merge k1 k2 = if sameKind k1 k2 then return k1
		  else fatal_error "merge: non-equal kinds"
		       $ posOfKind k1

sameClass :: Class -> Class -> Bool
sameClass(Intersection i1 _) (Intersection i2 _) = i1 == i2
sameClass (Downset t1) (Downset t2) = t1 == t2
sameClass _ _ = False

sameKind :: Kind -> Kind -> Bool
sameKind (ExtClass c1 v1 _) (ExtClass c2 v2 _) = 
    sameClass c1 c2 && v1 == v2
sameKind (KindAppl p1 c1 _) (KindAppl p2 c2 _) =
    sameKind p1 p2 && sameKind c1 c2
sameKind _ _ = False

instance Mergeable Class where
    merge c1@(Downset t1) (Downset t2) =
	if t1 == t2 then return c1
	   else fatal_error "merge: non-equal downset" $ posOfType t1
    merge c1@(Intersection i1 _) (Intersection i2 _) =
       if sort (nub i1) == sort (nub i2) then 
	      return c1
	  else fatal_error "merge: non-equal intersection class" $ 
	       posOfId $ head (i1 ++ i2)
    merge c _ = fatal_error "merge: class" $ posOfClass c

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
	    (TypeVarDefn, _) -> fail "merge TypeVarDefn"
	    (_, TypeVarDefn) -> fail "merge TypeVarDefn"
	    (NoTypeDefn, AliasTypeDefn sc) -> 
		fatal_error "merge: AliasTypeDefn" $ posOf [sc]
	    (AliasTypeDefn sc, NoTypeDefn) -> 
		fatal_error "merge: AliasTypeDefn" $ posOf [sc]
	    (NoTypeDefn, _) -> return d2
	    (_, NoTypeDefn) -> return d1
	    (_, _) -> if d1 == d2 then return d1 else
		      fail "merge TypeDefn"

instance Mergeable [OpInfo] where
-- this should be more sophisticated
    merge l1 l2 = mergeList l1 l2
