
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable
    

supply a simple data type for (precedence or subsort) relations. A
relation is conceptually a set of (ordered) pairs. 
But the hidden implementation is based on a map of sets.

'Rel' replaces a directed graph with unique node labels (Ord a) and
unlabelled edges (without multiplicity higher than one).

Usage: start with an 'empty' relation, 'insert' edges, and test for
an edge 'member' (before or after calling 'transClosure'). 

It is possible to insert self edges or bigger cycles.

A transitive path can be checked by 'transMember' without computing
the full transitive closure. A further 'insert', however,
may destroy the closedness property of a relation.

-}

module Common.Lib.Rel (Rel(), empty, isEmpty, insert, member, toMap,
                       union , subset, difference, transMember,
                       transClosure, fromList, toList, image,
                       restrict, toSet, fromSet, topSort) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

data Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Eq

-- | the empty relation
empty :: Rel a
empty = Rel Map.empty

-- | test for 'empty'
isEmpty :: Rel a -> Bool
isEmpty = Map.isEmpty . toMap 

-- | difference of two relations as set of pairs
difference :: Ord a => Rel a -> Rel a -> Rel a
difference a b = fromSet $ Set.difference  (toSet a) $ toSet b

-- | union of two relations as set of pairs
union :: Ord a => Rel a -> Rel a -> Rel a
union a b = fromSet $ Set.union (toSet a) $ toSet b

-- | is the first relation a subset of the second (viewed as set of pairs)
subset :: Ord a => Rel a -> Rel a -> Bool
subset a b = Set.subset (toSet a) $ toSet b

-- | insert an ordered pair
insert :: Ord a => a -> a -> Rel a -> Rel a
insert a b = let update = Map.setInsert a b in Rel . update . toMap

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
transClosure :: Ord a => Rel a -> Rel a
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
  Image (Added by T.M.) (implementation changed by C.M.)
--------------------------------------------------------------------}
-- | Image of a relation under a function
image :: (Ord a, Ord b) => (a -> b) -> Rel a -> Rel b
image f = fromSet . Set.image ( \ (a, b) -> (f a, f b)) . toSet

{--------------------------------------------------------------------
  Restriction (Added by T.M.)
--------------------------------------------------------------------}
-- | Restriction of a relation under a set
restrict :: Ord a => Rel a -> Set.Set a -> Rel a
restrict r s = 
  Rel
  $
  Map.foldWithKey
  (\a ra -> if a `Set.member` s 
             then case ra `Set.intersection` s of 
                    ra_s -> if Set.isEmpty ra_s 
                             then id
                             else Map.insert a ra_s
             else id)
  Map.empty
  $
  toMap r

{--------------------------------------------------------------------
 Conversion from/to sets (Added by T.M.)(implementation changed by C.M.)
--------------------------------------------------------------------}
-- | convert a relation to a set of ordered pairs
toSet :: (Ord a) => Rel a -> Set.Set (a, a)
toSet = Set.fromDistinctAscList . toList

-- | convert a set of ordered pairs to a relation 
fromSet :: (Ord a) => Set.Set (a, a) -> Rel a
fromSet = fromList . Set.toList

-- | topological sort a relation (more efficient for a closed relation)
topSort :: Ord a => Rel a -> [Set.Set a]
topSort r@(Rel m) = 
    if isEmpty r then []
    else let es = Set.unions $ Map.elems m
             ms = (Set.fromDistinctAscList $ Map.keys m) Set.\\ es in 
       if Set.isEmpty ms then let hasCyc = removeCycle r in 
           case hasCyc of 
           Nothing -> topSort (transClosure r)
           Just (a, cyc, restRel) ->
               map ( \ s -> if Set.member a s then 
                     Set.union s cyc else s) $ topSort restRel
        else let (lowM, rest) = 
                     Map.partitionWithKey (\ k _ -> Set.member k ms) m
                 -- no not forget loose ends 
                 bs = Set.unions $ Map.elems lowM
                 ls = bs Set.\\ Set.fromDistinctAscList (Map.keys rest) in 
                 -- put them as low as possible
            ms : (topSort $ Rel $ Set.fold ( \ i -> 
                      Map.insert i Set.empty) rest ls)

-- | try to remove a cycle
removeCycle :: Ord a => Rel a -> Maybe (a, Set.Set a, Rel a)
removeCycle r@(Rel m) = 
    let cycles = Map.filterWithKey Set.member m in
        if Map.isEmpty cycles then -- no cycle found 
           let cl = transClosure r in 
           if r == transClosure r then Nothing -- no cycle there 
              else removeCycle cl
           else let (a, os) = Map.findMin cycles
                    cs = Set.fold ( \ e s -> 
                            if member e a r then 
                                    Set.insert e s else s) Set.empty 
                         $ Set.delete a os
                    m1 = Map.map (Set.image ( \ e -> 
                                              if Set.member e cs then 
                                              a else e)) m 
                    rs = Map.foldWithKey ( \ k v s -> 
                                 if Set.member k cs then 
                                        Set.union s $ Set.delete a v else s) 
                         Set.empty m1
            in Just (a, cs, Rel $ Map.insert a rs $ Set.fold Map.delete m1 cs)

{- The result is a representative "a", the cycle "cs", i.e. all other
elements that are represented by "a" and the remaining relation with
all elements from "cs" replaced by "a" and without the cycle "(a,a)"
-}
