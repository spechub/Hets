
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable
    

supply a simple data type for (precedence or subsort) relations. A
relation is conceptually a set of (ordered) pairs (see 'toList' and
'fromList'). But the hidden implementation is based on a map of sets.

'Rel' replaces a directed graph with unique node labels (Ord a) and
unlabelled edges (without multiplicity higher than one).

Usage: start with an 'empty' relation, 'insert' edges, and test for
an edge 'member' (before or after calling 'transClosure'). 

It is possible to insert self edges or bigger cycles.

A transitive path can be checked by 'transMember' without computing
the full transitive closure. A further 'insert', however,
may destroy the closedness property of a relation.

Currently, no further functions seem to be necessary: 

- deletion

- filtering, mapping

- transposing

- reflexive closure (for a finite domain)

- computing a minimal relation whose transitive closure 
  covers a given relation

-}

module Common.Lib.Rel (Rel(), empty, isEmpty, insert, member, toMap
		      , transMember, transClosure, fromList, toList
                      , image, restrict, toSet, fromSet) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

newtype Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Eq

-- | the empty relation
empty :: Rel a
empty = Rel Map.empty

-- | test for 'empty'
isEmpty :: Rel a -> Bool
isEmpty = Map.isEmpty . toMap 

-- | insert an ordered pair
insert :: Ord a => a -> a -> Rel a -> Rel a
insert a b =
    let update m = Map.insert a ((b `Set.insert`) $ 
				 Map.findWithDefault Set.empty a m) m
    in 
    Rel . update .toMap

-- | test for an (previously inserted) ordered pair
member :: Ord a => a -> a -> Rel a -> Bool
member a b r = Set.member b $ getDAdjs r a

-- | get direct right neighbours   
getDAdjs :: Ord a => Rel a -> a -> Set.Set a
getDAdjs r a = Map.findWithDefault Set.empty a $ toMap r

-- | get right neighbours and right neighbours of right neighbours
getTAdjs :: Ord a => Rel a -> Set.Set a -> Set.Set a -> Set.Set a
-- transitive right neighbours
-- initial call 'getTAdjs succs r Set.empty $ Set.single a'
getTAdjs r given new =
    if Set.isEmpty new then given else 
    let ds = Set.unions $ map (getDAdjs r) $ Set.toList new in 
    getTAdjs r (ds `Set.union` given) (ds Set.\\ new Set.\\ given)

-- | test for 'member' or transitive membership
transMember :: Ord a => a -> a -> Rel a -> Bool
transMember a b r = Set.member b $ getTAdjs r Set.empty $ Set.single a

-- | compute transitive closure (make all transitive members direct members)
transClosure ::  Ord a => Rel a -> Rel a
transClosure r = Rel $ Map.map ( \ s -> getTAdjs r s s) $ toMap r

-- | convert a list of ordered pairs to a relation 
fromList :: Ord a => [(a, a)] -> Rel a
fromList = foldr (\ (a, b) r -> insert a b r ) empty

-- | convert a relation to a list of ordered pairs
toList ::  Ord a => Rel a -> [(a, a)]
toList = concatMap (\ (a , bs) -> map ( \ b -> (a, b) ) (Set.toList bs)) 
	 . Map.toList . toMap

instance (Show a, Ord a) => Show (Rel a) where
    show = show . Set.fromList . toList

{--------------------------------------------------------------------
  Image (Added by T.M.)
--------------------------------------------------------------------}
-- | /n/. Image of a relation under a function
image :: Ord b => (a -> b) -> Rel a -> Rel b
image f = Rel 
          .
          Map.foldWithKey 
           (\a ra -> Map.insert (f a) (Set.image f ra)) 
           Map.empty
          .
          toMap

{--------------------------------------------------------------------
  Restriction (Added by T.M.)
--------------------------------------------------------------------}
-- | /n/. Image of a relation under a function
restrict :: Ord a => Rel a -> Set.Set a -> Rel a
restrict r s = 
  Rel
  $
  Map.foldWithKey
  (\a ra -> if a `Set.member` s 
             then Map.insert a (ra `Set.intersection` s)
             else id)
  Map.empty
  $
  toMap r

{--------------------------------------------------------------------
 Conversion from/to sets (Added by T.M.)
--------------------------------------------------------------------}
toSet :: (Ord a) => Rel a -> Set.Set (a, a)
toSet = Map.foldWithKey (\a ra -> Set.fold (\b -> (Set.insert (a,b) .) ) id ra) Set.empty 
        . toMap

fromSet :: (Ord a) => Set.Set (a, a) -> Rel a
fromSet = Rel .
          Set.fold (\(a,b) -> Map.setInsert a b) Map.empty
