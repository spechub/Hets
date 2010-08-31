{- |
Module      :  $Header$
Description :  Utils extending Data.Set and Data.Map
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}

module Search.Utils.SetMap where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map


dom :: (Ord a) => Map.Map a b -> Set.Set a
dom = Set.fromList . Map.keys

cod :: (Ord a,Ord b) => Map.Map a b -> Set.Set b
cod = Set.fromList . Map.elems

zipValues :: (Ord a,Ord b,Ord c) => Set.Set a -> Map.Map a b -> Map.Map a c -> Set.Set (b,c)
zipValues commonSupport f g = Set.map  mkPair commonSupport
    where mkPair a = case (Map.lookup a f,Map.lookup a g)
		     of (Just b,Just c) -> (b,c)
			_ -> error "fail to zip maps outside common support"

image :: (Ord a,Ord b) => Map.Map a b -> Set.Set a -> Set.Set b
image m s = theImage
    where mlist = Map.toList m
	  pairs = filter (\p -> Set.member (fst p) s) mlist
	  theImage = Set.fromList (map snd pairs)

restrictDomByCod :: (Ord a,Ord b) => Map.Map a b -> (b -> Bool) -> Set.Set a
restrictDomByCod m p = Set.fromList (map fst (filter (p . snd) (Map.toList m)))

restrictCodByCod :: (Ord a,Ord b) => Map.Map a b -> (b -> Bool) -> Set.Set b
restrictCodByCod m p = Set.fromList (map snd (filter (p . snd) (Map.toList m)))

fromListSetValues :: (Ord k,Ord v) => [(k,v)] -> Map.Map k (Set.Set v)
fromListSetValues lst = foldr updateMap Map.empty lst
    where updateMap (k,v) m =
	      case Map.lookup k m
	      of (Just vs) -> Map.insert k (Set.insert v vs) m
		 Nothing -> Map.insert k (Set.singleton v) m

fromSetSetValues :: (Ord k,Ord v) => Set.Set (k,v) -> Map.Map k (Set.Set v)
fromSetSetValues set = Set.fold updateMap Map.empty set
    where updateMap (k,v) m =
	      case Map.lookup k m
	      of (Just vs) -> Map.insert k (Set.insert v vs) m
		 Nothing -> Map.insert k (Set.singleton v) m




{-
*Utils.SetMap> fromListSetValues [(1,4),(2,4),(1,3)]
{1:={3,4},2:={4}}
-}

fromList :: (Ord a,Ord b) => [(a,b)] -> Maybe (Map.Map a b)
fromList lst = 
    if Map.size fun == length lst' then Just fun else Nothing
    where lst' = List.nub lst
	  fun = Map.fromList lst'

{-| 
  fromList takes a list of pairs interpretes it as relation and
  returns it as a Just Map if the relation is right unique and Nothing
  otherwise; e.g.
  * fromList [(1,1),(1,1),(2,1)] -> Just (fromList [(1,1),(2,1)])
  * fromList [(1,1),(1,2),(2,1)] -> Nothing
-}

maybeUnion :: (Ord a,Ord b) => Map.Map a b -> Map.Map a b -> Maybe (Map.Map a b)
maybeUnion m1 m2 = nextMin Map.empty m1 m2


nextMin m m1 m2 = 
    if (Map.null m1) || (Map.null m2)
    then Just $ Map.unions [m,m1,m2]
    else let ((k1,v1),m1') = Map.deleteFindMin m1
             ((k2,v2),m2') = Map.deleteFindMin m2
             insertMin (k,v) n1 n2 = nextMin (Map.insert k v m) n1 n2
         in if k1 == k2 && v1 /= v2
            then Nothing
            else case compare (k1,v1) (k2,v2)
                 of LT -> nextMin (Map.insert k1 v1 m) m1' m2
                    EQ -> nextMin (Map.insert k1 v1 m) m1' m2'
                    GT -> nextMin (Map.insert k2 v2 m) m1 m2'

{-
m1 = Map.fromList [(1,6),(2,7),(3,8)]
m2 = Map.fromList [(1,6),(3,6),(4,8)]
m3 = Map.fromList [(1,6),(5,6),(4,8)]
> maybeUnion m1 m2
Nothing
> maybeUnion m1 m3
Just (fromList [(1,6),(2,7),(3,8),(4,8),(5,6)])
> maybeUnion m1 m1
Just (fromList [(1,6),(2,7),(3,8)])
> maybeUnion m3 m1
Just (fromList [(1,6),(2,7),(3,8),(4,8),(5,6)])
-}