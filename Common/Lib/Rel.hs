{- |
Module      :  $Header$
Description :  Relations, based on maps
Copyright   :  (c) Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

supply a simple data type for (precedence or subsort) relations. A
relation is conceptually a set of (ordered) pairs,
but the hidden implementation is based on a map of sets.
An alternative view is that of a directed Graph
without isolated nodes.

'Rel' is a directed graph with elements (Ord a) as (uniquely labelled) nodes
and (unlabelled) edges (with a multiplicity of at most one).

Usage: start with an 'empty' relation, 'insert' edges, and test for
an edge 'member' (before or after calling 'transClosure').

It is possible to insert self edges or bigger cycles.

Checking for a 'path' corresponds to checking for a member in the
transitive (possibly non-reflexive) closure. A further 'insert', however,
may destroy the closedness property of a relation.

-}

module Common.Lib.Rel
    ( Rel, map
    , MapSet.null, MapSet.empty, MapSet.member
    , MapSet.toMap, MapSet.insert, MapSet.union
    , MapSet.intersection, MapSet.difference
    , MapSet.transpose
    , MapSet.setToMap
    , isSubrelOf, path
    , succs, predecessors, irreflex, sccOfClosure
    , transClosure, fromList, toList, toPrecMap
    , intransKernel, mostRight, restrict, delSet
    , toSet, fromSet, topSort, nodes, collaps
    , transReduce
    , locallyFiltered
    , flatSet, partSet, partList, leqClasses
    ) where

import Prelude hiding (map, null)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

import qualified Common.Lib.MapSet as MapSet

type Rel a = MapSet.MapSet a a

-- | is the first relation a sub-relation of the second
isSubrelOf :: Ord a => Rel a -> Rel a -> Bool
isSubrelOf = MapSet.isSubmapOf

-- | get direct successors
succs :: Ord a => Rel a -> a -> Set.Set a
succs = flip MapSet.lookup

-- | get all transitive successors
reachable :: Ord a => Rel a -> a -> Set.Set a
reachable r a = Set.fold reach Set.empty $ succs r a where
    reach e s = if Set.member e s then s
                    else Set.fold reach (Set.insert e s) $ succs r e

-- | predecessors of one node in the given set of a nodes
preds :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> b -> Set.Set a -> Set.Set a
preds m a = Set.filter ( \ s -> MapSet.setMember s a m)

-- | get direct predecessors inefficiently
predecessors :: Ord a => Rel a -> a -> Set.Set a
predecessors r a = let m = MapSet.toMap r in preds m a $ Map.keysSet m

-- | test for 'member' or transitive membership (non-empty path)
path :: Ord a => a -> a -> Rel a -> Bool
path a b r = Set.member b $ reachable r a

-- | compute transitive closure (make all transitive members direct members)
transClosure :: Ord a => Rel a -> Rel a
transClosure r = MapSet.fromDistinctMap
  . Map.mapWithKey ( \ k _ -> reachable r k) $ MapSet.toMap r

-- | make relation irreflexive
irreflex :: Ord a => Rel a -> Rel a
irreflex = MapSet.fromMap . Map.mapWithKey Set.delete . MapSet.toMap

-- | compute strongly connected components for a transitively closed relation
sccOfClosureM :: Ord a => Map.Map a (Set.Set a) -> [Set.Set a]
sccOfClosureM m =
        if Map.null m then []
        else let ((k, v), p) = Map.deleteFindMin m in
             if Set.member k v then -- has a cycle
                let c = preds m k v in -- get the cycle
                c : sccOfClosureM (Set.fold Map.delete p c)
             else sccOfClosureM p

-- | compute strongly connected components for a transitively closed relation
sccOfClosure :: Ord a => Rel a -> [Set.Set a]
sccOfClosure = sccOfClosureM . MapSet.toMap

-- | restrict to elements not in the input set
delSetM :: Ord a => Set.Set a -> Map.Map a (Set.Set a) -> Map.Map a (Set.Set a)
delSetM s m = Map.map (Set.\\ s) $ m Map.\\ MapSet.setToMap s

-- | restrict to elements not in the input set
delSet :: Ord a => Set.Set a -> Rel a -> Rel a
delSet s = MapSet.fromMap . delSetM s . MapSet.toMap

{- | restrict strongly connected components to its minimal representative
     (input sets must be non-null). Direct cycles may remain. -}
collaps :: Ord a => [Set.Set a] -> Rel a -> Rel a
collaps = delSet . Set.unions . List.map Set.deleteMin

{- | transitive reduction (minimal relation with the same transitive closure)
     of a transitively closed DAG (i.e. without cycles)! -}
transReduce :: Ord a => Rel a -> Rel a
transReduce r = let m = MapSet.toMap r in MapSet.fromMap $
-- keep all (i, j) in rel for which no c with (i, c) and (c, j) in rel
    Map.mapWithKey ( \ i s -> let d = MapSet.setToMap $ Set.delete i s in
        Set.filter ( \ j ->
            Map.null $ Map.filter (Set.member j)
                $ Map.intersection m $ Map.delete j d) s) m

-- | convert a list of ordered pairs to a relation
fromList :: Ord a => [(a, a)] -> Rel a
fromList = foldr (uncurry MapSet.insert) MapSet.empty

-- | convert a relation to a list of ordered pairs
toList :: Rel a -> [(a, a)]
toList = concatMap (\ (a, bs) -> List.map (\ b -> (a, b)) bs)
  . MapSet.toList

-- | map the values of a relation
map :: (Ord a, Ord b) => (a -> b) -> Rel a -> Rel b
map f = MapSet.foldWithKey
    ( \ a b -> MapSet.insert (f a) $ f b) MapSet.empty

-- | Restriction of a relation under a set
restrict :: Ord a => Rel a -> Set.Set a -> Rel a
restrict r s = delSet (nodes r Set.\\ s) r

-- | convert a relation to a set of ordered pairs
toSet :: (Ord a) => Rel a -> Set.Set (a, a)
toSet = Set.fromDistinctAscList . toList

-- | convert a set of ordered pairs to a relation
fromSet :: (Ord a) => Set.Set (a, a) -> Rel a
fromSet = fromAscList . Set.toList

-- | convert a sorted list of ordered pairs to a relation
fromAscList :: (Ord a) => [(a, a)] -> Rel a
fromAscList = MapSet.fromDistinctMap
  . Map.fromDistinctAscList
  . List.map ( \ l -> (fst (head l),
                       Set.fromDistinctAscList $ List.map snd l))
  . List.groupBy ( \ (a, _) (b, _) -> a == b)

-- | all nodes of the edges
nodes :: Ord a => Rel a -> Set.Set a
nodes r = Set.union (MapSet.keysSet r) $ MapSet.elems r

topSortDAGM :: Ord a => Map.Map a (Set.Set a) -> [Set.Set a]
topSortDAGM m = if Map.null m then [] else
    let es = MapSet.setElems m
        ml = Map.keysSet m Set.\\ es -- most left
        m2 = delSetM ml m
        rs = es Set.\\ Map.keysSet m2 -- re-insert loose ends
    in ml : topSortDAGM (Set.fold (`Map.insert` Set.empty) m2 rs)

topSortDAG :: Ord a => Rel a -> [Set.Set a]
topSortDAG = topSortDAGM . MapSet.toMap

-- | topologically sort a closed relation (ignore isolated cycles)
topSort :: Ord a => Rel a -> [Set.Set a]
topSort r = let cs = sccOfClosure r in
      List.map (expandCycle cs) $ topSortDAG $ irreflex $ collaps cs r

{- | Construct a precedence map from a closed relation. Indices range
   between 1 and the second value that is output. -}
toPrecMap :: Ord a => Rel a -> (Map.Map a Int, Int)
toPrecMap = foldl ( \ (m1, c) s -> let n = c + 1 in
                    (Set.fold (`Map.insert` n) m1 s, n))
                 (Map.empty, 0) . topSort

-- | find the cycle and add it to the result set
expandCycle :: Ord a => [Set.Set a] -> Set.Set a -> Set.Set a
expandCycle cs s = case cs of
  [] -> s
  c : r -> if Set.null c then error "Common.Lib.Rel.expandCycle" else
    let (a, b) = Set.deleteFindMin c in
    if Set.member a s then Set.union b s else expandCycle r s

{- | gets the most right elements of the irreflexive relation,
     unless no hierarchy is left then isolated nodes are output -}
mostRightOfCollapsed :: Ord a => Rel a -> Set.Set a
mostRightOfCollapsed r = if MapSet.null r then Set.empty
    else let ir = irreflex r
             mr = MapSet.elems ir Set.\\ MapSet.keysSet ir
         in if Set.null mr then Map.keysSet $ Map.filterWithKey
                ((==) . Set.singleton) $ MapSet.toMap r
            else mr

{- |
find s such that x in s => forall y . yRx or not yRx and not xRy

 * precondition: (transClosure r == r)

 * strongly connected components (cycles) are treated as a compound node
-}

mostRight :: Ord a => Rel a -> Set.Set a
mostRight r = let
    cs = sccOfClosure r
    in expandCycle cs (mostRightOfCollapsed $ collaps cs r)

{- |
intransitive kernel of a reflexive and transitive closure

 * precondition: (transClosure r == r)
 * cycles are uniquely represented (according to Ord)
-}
intransKernel :: Ord a => Rel a -> Rel a
intransKernel r =
    let cs = sccOfClosure r
    in foldr addCycle (transReduce $ collaps cs r) cs

-- | add a cycle given by a set in the collapsed node
addCycle :: Ord a => Set.Set a -> Rel a -> Rel a
addCycle c r = if Set.null c then error "Common.Lib.Rel.addCycle" else
    let (a, b) = Set.deleteFindMin c
        (m, d) = Set.deleteFindMax c
    in MapSet.insert m a $ foldr (uncurry MapSet.insert) (MapSet.delete a a r) $
       zip (Set.toList d) (Set.toList b)

{- | calculates if two given elements have a common left element

 * if one of the arguments is not present False is returned
-}
haveCommonLeftElem :: Ord a => a -> a -> Rel a -> Bool
haveCommonLeftElem t1 t2 =
    Map.fold (\ e -> (|| Set.member t1 e && Set.member t2 e)) False
    . MapSet.toMap

{- | partitions a set into a list of disjoint non-empty subsets
determined by the given function as equivalence classes -}
partSet :: Ord a => (a -> a -> Bool) -> Set.Set a -> [Set.Set a]
partSet f = List.map Set.fromList . leqClasses f

{- | partitions a list into a list of disjoint non-empty lists
determined by the given function as equivalence classes -}
partList :: (a -> a -> Bool) -> [a] -> [[a]]
partList f l = case l of
  [] -> []
  x : r -> let
    (ds, es) = List.partition (not . any (f x)) $ partList f r
    in (x : concat es) : ds

-- | Divide a Set (List) into equivalence classes w.r.t. eq
leqClasses :: Ord a => (a -> a -> Bool) -> Set.Set a -> [[a]]
leqClasses f = partList f . Set.toList

{- | flattens a list of non-empty sets and uses the minimal element of
each set to represent the set -}
flatSet :: Ord a => [Set.Set a] -> Set.Set a
flatSet = Set.fromList . List.map (\ s -> if Set.null s
                         then error "Common.Lib.Rel.flatSet"
                         else Set.findMin s)

{- | checks if a given relation is locally filtered

 * precondition: the relation must already be closed by transitive closure
-}
locallyFiltered :: Ord a => Rel a -> Bool
locallyFiltered rel = check . flatSet . partSet iso $ mostRight rel
    where iso x y = MapSet.member x y rel && MapSet.member y x rel
          check s = Set.null s ||
                  Set.fold (\ y ->
                            (&& not (haveCommonLeftElem x y rel))) True s'
                  && check s'
              where (x, s') = Set.deleteFindMin s
