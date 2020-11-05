{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/Lib/Rel.hs
Description :  Relations, based on maps
Copyright   :  (c) Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

supply a simple data type for (precedence or subsort) relations. A
relation is conceptually a set of (ordered) pairs,
but the hidden implementation is based on a map of sets.
An alternative view is that of a directed Graph possibly
with isolated nodes.

'Rel' is a directed graph with elements (Ord a) as (uniquely labelled) nodes
and (unlabelled) edges (with a multiplicity of at most one).

Usage: start with an 'empty' relation, 'insert' edges, and test for
an edge 'member' (before or after calling 'transClosure').

It is possible to insert self edges or bigger cycles.  But rather than
inserting self edges and element can be mapped to the empty set.

Checking for a 'path' corresponds to checking for a member in the
transitive (possibly non-reflexive) closure. A further 'insert', however,
may destroy the closedness property of a relation.

-}

module Common.Lib.Rel
    ( Rel, empty, nullKeys, rmNullSets
    , insertPair, insertDiffPair, insertKeyOrPair
    , member, toMap, map
    , noPairs, insertKey, deleteKey, memberKey, keysSet
    , fromKeysSet
    , reflexive
    , getCycles
    , union, intersection, isSubrelOf, difference, path
    , delete, succs, predecessors, irreflex, sccOfClosure
    , transClosure, fromList, toList, toPrecMap
    , intransKernel, mostRight, restrict, delSet
    , toSet, fromSet, topSort, depSort, nodes, collaps
    , transpose, transReduce
    , fromMap, locallyFiltered
    , flatSet, partSet, partList, leqClasses
    ) where

import Prelude hiding (map, null)
import Data.Data
import Data.Hashable
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set
import qualified Data.List as List

import qualified Common.Lib.MapSet as MapSet

-- | no invariant is ensured for relations!
newtype Rel a = Rel { toMap :: Map.HashMap a (Set.Set a) }
  deriving (Eq, Ord, Typeable, Data)

instance Show a => Show (Rel a) where
    show = show . toMap

instance (Ord a, Read a, Hashable a) => Read (Rel a) where
    readsPrec d = List.map (\ (m, r) -> (fromMap m , r)) . readsPrec d

fromMap :: Map.HashMap a (Set.Set a) -> Rel a
fromMap = Rel

-- | the empty relation
empty :: Rel a
empty = Rel Map.empty

-- | test for 'empty'
nullKeys :: Rel a -> Bool
nullKeys (Rel m) = Map.null m

-- | keys of the relation
keysSet :: (Ord a, Hashable a) => Rel a -> Set.Set a
keysSet = Set.fromList . Map.keys . toMap

rmNullSets :: (Ord a, Hashable a) => Rel a -> Rel a
rmNullSets = Rel . MapSet.rmNullSets . toMap

-- | test for 'empty'
noPairs :: (Ord a, Hashable a) => Rel a -> Bool
noPairs = nullKeys . rmNullSets

-- | difference of two relations
difference :: (Ord a, Hashable a) => Rel a -> Rel a -> Rel a
difference (Rel m) = Rel . Map.differenceWith MapSet.setDifference m . toMap

-- | union of two relations
union :: (Ord a, Hashable a) => Rel a -> Rel a -> Rel a
union (Rel m) = Rel . Map.unionWith Set.union m . toMap

-- | intersection of two relations
intersection :: (Ord a, Hashable a)=> Rel a -> Rel a -> Rel a
intersection (Rel m) = Rel . Map.intersectionWith Set.intersection m . toMap

-- | is the first relation a sub-relation of the second
isSubrelOf :: (Ord a, Hashable a) => Rel a -> Rel a -> Bool
isSubrelOf (Rel m) = Map.isSubmapOfBy Set.isSubsetOf m . toMap

-- | insert an ordered pair
insertPair :: (Ord a, Hashable a) => a -> a -> Rel a -> Rel a
insertPair a b = Rel . MapSet.setInsert a b . toMap

-- | insert a pair only if both sides are different
insertDiffPair :: (Ord a, Hashable a) => a -> a -> Rel a -> Rel a
insertDiffPair a b = if a == b then id else insertPair a b

-- | insert a pair only if both sides are different
insertKeyOrPair :: (Ord a, Hashable a) => a -> a -> Rel a -> Rel a
insertKeyOrPair a b = if a == b then insertKey a else insertPair a b

-- | insert an unrelated node
insertKey :: (Ord a, Hashable a) => a -> Rel a -> Rel a
insertKey k r@(Rel m) = if Map.member k m then r else
  Rel $ Map.insert k Set.empty m

-- | delete an ordered pair
delete :: (Ord a, Hashable a) => a -> a -> Rel a -> Rel a
delete a b (Rel m) =
    let t = Set.delete b $ MapSet.setLookup a m in
    Rel $ if Set.null t then Map.delete a m else Map.insert a t m

-- | delete a node and all its relations
deleteKey :: (Ord a, Hashable a) => a -> Rel a -> Rel a
deleteKey k = Rel . Map.delete k . toMap

-- | test for an (previously inserted) ordered pair
member :: (Ord a, Hashable a) => a -> a -> Rel a -> Bool
member a b r = Set.member b $ succs r a

memberKey :: (Ord a, Hashable a) => a -> Rel a -> Bool
memberKey k = Map.member k . toMap

-- | get direct successors
succs :: (Ord a, Hashable a) => Rel a -> a -> Set.Set a
succs (Rel m) a = Map.findWithDefault Set.empty a m

-- | get all transitive successors
reachable :: (Ord a, Hashable a) => Rel a -> a -> Set.Set a
reachable r a = Set.fold reach Set.empty $ succs r a where
    reach e s = if Set.member e s then s
                    else Set.fold reach (Set.insert e s) $ succs r e

-- | predecessors of one node in the given set of a nodes
preds :: (Ord a, Hashable a) => Rel a -> a -> Set.Set a -> Set.Set a
preds r a = Set.filter ( \ s -> member s a r)

-- | get direct predecessors
predecessors :: (Ord a, Hashable a) => Rel a -> a -> Set.Set a
predecessors (Rel m) a = Set.fromList $ Map.keys $ Map.filter (Set.member a) m

-- | test for 'member' or transitive membership (non-empty path)
path :: (Ord a, Hashable a) => a -> a -> Rel a -> Bool
path a b r = Set.member b $ reachable r a

-- | compute transitive closure (make all transitive members direct members)
transClosure :: (Ord a, Hashable a) => Rel a -> Rel a
transClosure r@(Rel m) = Rel $ Map.mapWithKey ( \ k _ -> reachable r k) m

-- | get transposed relation (losing unrelated keys)
transpose :: (Ord a, Hashable a) => Rel a -> Rel a
transpose = Rel . MapSet.toMap . MapSet.transpose . MapSet.fromMap . toMap

-- | make relation irreflexive
irreflex :: (Ord a, Hashable a) => Rel a -> Rel a
irreflex = Rel . Map.mapWithKey Set.delete . toMap

-- | add all keys as reflexive elements
reflexive :: (Ord a, Hashable a) => Rel a -> Rel a
reflexive = Rel . Map.mapWithKey Set.insert . toMap

-- | get entries that contain the key as element
getCycles :: (Ord a, Hashable a) => Rel a -> Rel a
getCycles = Rel . Map.filterWithKey Set.member . toMap

-- | compute strongly connected components for a transitively closed relation
sccOfClosure :: (Ord a, Hashable a) => Rel a -> [Set.Set a]
sccOfClosure r@(Rel m) =
        if Map.null m then []
        else let mList = List.sortOn fst $ Map.toList m
                 scc l = 
                  case l of 
                   [] -> []
                   (k, v):t ->  
                     if Set.member k v then -- has a cycle
                       let c = preds r k v in -- get the cycle
                       c : sccOfClosure (delSet c $ Rel $ Map.fromList t) 
                                        -- TODO: this is very inefficient
                     else scc t 
             in scc mList
                 

{- | restrict strongly connected components to its minimal representative
     (input sets must be non-null). Direct cycles may remain. -}
collaps :: (Ord a, Hashable a) => [Set.Set a] -> Rel a -> Rel a
collaps = delSet . Set.unions . List.map Set.deleteMin

{- | transitive reduction (minimal relation with the same transitive closure)
     of a transitively closed DAG (i.e. without cycles)! -}
transReduce :: (Ord a, Hashable a) => Rel a -> Rel a
transReduce (Rel m) = Rel
-- keep all (i, j) in rel for which no c with (i, c) and (c, j) in rel
  $ Map.mapWithKey ( \ i s -> let d = MapSet.setToMap $ Set.delete i s in
        Set.filter ( \ j ->
            Map.null $ Map.filter (Set.member j)
                $ Map.intersection m $ Map.delete j d) s) m

-- | convert a list of ordered pairs to a relation
fromList :: (Ord a, Hashable a) => [(a, a)] -> Rel a
fromList = foldr (uncurry insertPair) empty

-- | convert a relation to a list of ordered pairs (this loses isolated keys!)
toList :: (Ord a, Hashable a) => Rel a -> [(a, a)]
toList (Rel m) = concatMap (\ (a , bs) -> List.map ( \ b -> (a, b) )
                            (Set.toList bs)) $ Map.toList m

-- | map the values of a relation
map :: (Ord a, Ord b, Hashable a, Hashable b) => (a -> b) -> Rel a -> Rel b
map f (Rel m) = -- Rel $ Map.foldl' (\) Map.empty Map.mapKeysWith Set.union f 
  let m' = Map.map (Set.map f) m
  in Rel $ Map.fromList $ 
           List.map (\(x, y) -> (f x, y)) $
           Map.toList $
      List.foldl' (\f0 (k,v) -> 
                if k `elem` Map.keys f0 
                then Map.adjust (Set.union v) k f0
                else Map.insert k v f0) 
      Map.empty $ Map.toList m'

-- | Restriction of a relation under a set
restrict :: (Ord a, Hashable a) => Rel a -> Set.Set a -> Rel a
restrict r s = delSet (nodes r Set.\\ s) r

-- | restrict to elements not in the input set
delSet :: (Ord a, Hashable a) => Set.Set a -> Rel a -> Rel a
delSet s (Rel m) = Rel $ Map.map (Set.\\ s) $ Map.difference m $ MapSet.setToMap s

-- | convert a relation to a set of ordered pairs
toSet :: (Ord a, Hashable a) => Rel a -> Set.Set (a, a)
toSet = Set.fromDistinctAscList . toList

-- | convert a set of ordered pairs to a relation
fromSet :: (Ord a, Hashable a) => Set.Set (a, a) -> Rel a
fromSet = fromAscList . Set.toList

-- | convert a plain node set to a relation
fromKeysSet :: (Ord a, Hashable a) => Set.Set a -> Rel a
fromKeysSet = Rel . Set.fold (`Map.insert` Set.empty) Map.empty

-- | convert a sorted list of ordered pairs to a relation
fromAscList :: (Ord a, Hashable a) => [(a, a)] -> Rel a
fromAscList = Rel . Map.fromList
                  . List.map ( \ l -> (fst (head l),
                                  Set.fromDistinctAscList $ List.map snd l))
                        . List.groupBy ( \ (a, _) (b, _) -> a == b)

-- | all nodes of the edges
nodes :: (Ord a, Hashable a) => Rel a -> Set.Set a
nodes (Rel m) = Set.union (Set.fromList $ Map.keys m) $ MapSet.setElems m

{- | Construct a precedence map from a closed relation. Indices range
   between 1 and the second value that is output. -}
toPrecMap :: (Ord a, Hashable a) => Rel a -> (Map.HashMap a Int, Int)
toPrecMap = foldl ( \ (m1, c) s -> let n = c + 1 in
                    (Set.fold (`Map.insert` n) m1 s, n))
                 (Map.empty, 0) . topSort

topSortDAG :: (Ord a, Hashable a) => Rel a -> [Set.Set a]
topSortDAG r@(Rel m) = if Map.null m then [] else
    let es = MapSet.setElems m
        ml = (Set.fromList $ Map.keys m) Set.\\ es -- most left
        Rel m2 = delSet ml r
        rs = es Set.\\ (Set.fromList $ Map.keys m2) -- re-insert loose ends
    in ml : topSortDAG (Rel $ Set.fold (`Map.insert` Set.empty) m2 rs)

-- | topologically sort a closed relation (ignore isolated cycles)
topSort :: (Ord a, Hashable a) => Rel a -> [Set.Set a]
topSort r = let cs = sccOfClosure r in
      List.map (expandCycle cs) $ topSortDAG $ irreflex $ collaps cs r

-- | find the cycle and add it to the result set
expandCycle :: (Ord a, Hashable a) => [Set.Set a] -> Set.Set a -> Set.Set a
expandCycle cs s = case cs of
  [] -> s
  c : r ->
    if Set.null $ Set.intersection c s then expandCycle r s else Set.union c s

-- dependency sort
depSort :: (Ord a, Hashable a) => Rel a -> [Set.Set a]
depSort r = let cs = sccOfClosure r in
  List.concatMap (List.map (depCycle cs) . Set.toList)
    $ topSortDAG $ irreflex $ collaps cs r

depCycle :: (Ord a, Hashable a) => [Set.Set a] -> a -> Set.Set a
depCycle cs a = case cs of
  [] -> Set.singleton a
  c : r ->
    if Set.member a c then c else depCycle r a

-- | gets the most right elements of a relation,
mostRightOfCollapsed :: (Ord a, Hashable a) => Rel a -> Set.Set a
mostRightOfCollapsed r@(Rel m) =
  Set.difference (nodes r) . (Set.fromList . Map.keys) $ Map.filterWithKey
  (\ i s -> not (Set.null s) && s /= Set.singleton i) m

{- |
find s such that x in s => forall y . yRx or not yRx and not xRy

 * precondition: (transClosure r == r)

 * strongly connected components (cycles) are treated as a compound node
-}

mostRight :: (Ord a, Hashable a) => Rel a -> Set.Set a
mostRight r = let
    cs = sccOfClosure r
    in expandCycle cs (mostRightOfCollapsed $ collaps cs r)

{- |
intransitive kernel of a reflexive and transitive closure

 * precondition: (transClosure r == r)
 * cycles are uniquely represented (according to Ord)
-}
intransKernel :: (Ord a, Hashable a) => Rel a -> Rel a
intransKernel r =
    let cs = sccOfClosure r
    in foldr addCycle (transReduce $ collaps cs r) cs

-- add a cycle given by a set in the collapsed node
addCycle :: (Ord a, Hashable a) => Set.Set a -> Rel a -> Rel a
addCycle c r = if Set.null c then error "Common.Lib.Rel.addCycle" else
    let (a, b) = Set.deleteFindMin c
        (m, d) = Set.deleteFindMax c
    in insertPair m a $ foldr (uncurry insertPair) (delete a a r) $
       zip (Set.toList d) (Set.toList b)

{- | calculates if two given elements have a common left element

 * if one of the arguments is not present False is returned
-}
haveCommonLeftElem :: (Ord a, Hashable a) => a -> a -> Rel a -> Bool
haveCommonLeftElem t1 t2 =
    Map.foldr' (\ e -> (|| Set.member t1 e && Set.member t2 e)) False . toMap

{- | partitions a set into a list of disjoint non-empty subsets
determined by the given function as equivalence classes -}
partSet :: (Ord a, Hashable a) => (a -> a -> Bool) -> Set.Set a -> [Set.Set a]
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
leqClasses :: (Ord a, Hashable a) => (a -> a -> Bool) -> Set.Set a -> [[a]]
leqClasses f = partList f . Set.toList

{- | flattens a list of non-empty sets and uses the minimal element of
each set to represent the set -}
flatSet :: (Ord a, Hashable a) => [Set.Set a] -> Set.Set a
flatSet = Set.fromList . List.map (\ s -> if Set.null s
                         then error "Common.Lib.Rel.flatSet"
                         else Set.findMin s)

{- | checks if a given relation is locally filtered

 * precondition: the relation must already be closed by transitive closure
-}
locallyFiltered :: (Ord a, Hashable a) => Rel a -> Bool
locallyFiltered rel = check . flatSet . partSet iso $ mostRight rel
    where iso x y = member x y rel && member y x rel
          check s = Set.null s ||
                  Set.fold (\ y ->
                            (&& not (haveCommonLeftElem x y rel))) True s'
                  && check s'
              where (x, s') = Set.deleteFindMin s
