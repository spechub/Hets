{- |
Module      :  $Header$
Description :  Relations, based on maps
Copyright   :  (c) Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

The functions 'image', and 'setInsert' are utility functions
for plain maps involving sets.

-}

module Common.Lib.Rel
    ( Rel(), empty, null, insert, member, toMap, map
    , union , isSubrelOf, difference, path, delete
    , succs, predecessors, irreflex, sccOfClosure
    , transClosure, fromList, toList, image, toPrecMap
    , intransKernel, mostRight, restrict, delSet
    , toSet, fromSet, topSort, nodes
    , transpose, transReduce, setInsert
    , fromDistinctMap, locallyFiltered, flatSet, partSet
    ) where

import Prelude hiding (map, null)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

data Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Eq
-- the invariant is that set values are never empty

fromDistinctMap :: Map.Map a (Set.Set a) -> Rel a
fromDistinctMap = Rel

-- | the empty relation
empty :: Rel a
empty = Rel Map.empty

-- | test for 'empty'
null :: Rel a -> Bool
null (Rel m) = Map.null m

-- | difference of two relations
difference :: Ord a => Rel a -> Rel a -> Rel a
difference a b = fromSet (toSet a Set.\\ toSet b)

-- | union of two relations
union :: Ord a => Rel a -> Rel a -> Rel a
union a b = fromSet $ Set.union (toSet a) $ toSet b

-- | is the first relation a sub-relation of the second
isSubrelOf :: Ord a => Rel a -> Rel a -> Bool
isSubrelOf a b = Set.isSubsetOf (toSet a) $ toSet b

-- | insert an ordered pair
insert :: Ord a => a -> a -> Rel a -> Rel a
insert a b = Rel . setInsert a b . toMap

-- | delete an ordered pair
delete :: Ord a => a -> a -> Rel a -> Rel a
delete a b (Rel m) =
    let t = Set.delete b $ Map.findWithDefault Set.empty a m in
    Rel $ if Set.null t then Map.delete a m else Map.insert a t m

-- | test for an (previously inserted) ordered pair
member :: Ord a => a -> a -> Rel a -> Bool
member a b r = Set.member b $ succs r a

-- | get direct successors
succs :: Ord a => Rel a -> a -> Set.Set a
succs (Rel m) a = Map.findWithDefault Set.empty a m

-- | get all transitive successors
reachable :: Ord a => Rel a -> a -> Set.Set a
reachable r a = Set.fold reach Set.empty $ succs r a where
    reach e s = if Set.member e s then s
                    else Set.fold reach (Set.insert e s) $ succs r e

-- | predecessors of one node in the given set of a nodes
preds :: Ord a => Rel a -> a -> Set.Set a -> Set.Set a
preds r a = Set.filter ( \ s -> member s a r)

-- | get direct predecessors inefficiently
predecessors :: Ord a => Rel a -> a -> Set.Set a
predecessors r@(Rel m) a = preds r a $ Map.keysSet m

-- | test for 'member' or transitive membership (non-empty path)
path :: Ord a => a -> a -> Rel a -> Bool
path a b r = Set.member b $ reachable r a

-- | compute transitive closure (make all transitive members direct members)
transClosure :: Ord a => Rel a -> Rel a
transClosure r@(Rel m) = Rel $ Map.mapWithKey ( \ k _ -> reachable r k) m

-- | get reverse relation
transpose :: Ord a => Rel a -> Rel a
transpose = fromList . List.map ( \ (a, b) -> (b, a)) . toList

-- | establish the invariant
rmNull :: Ord a => Map.Map a (Set.Set a) -> Map.Map a (Set.Set a)
rmNull = Map.filter (not . Set.null)

-- | make relation irreflexive
irreflex :: Ord a => Rel a -> Rel a
irreflex (Rel m) = Rel $ rmNull $ Map.mapWithKey (Set.delete) m

-- | compute strongly connected components for a transitively closed relation
sccOfClosure :: Ord a => Rel a -> [Set.Set a]
sccOfClosure r@(Rel m) =
        if Map.null m then []
        else let ((k, v), p) = Map.deleteFindMin m in
             if Set.member k v then -- has a cycle
                let c = preds r k v in -- get the cycle
                c : sccOfClosure (Rel $ Set.fold Map.delete p c)
             else sccOfClosure (Rel p)

{- | restrict strongly connected components to its minimal representative
     (input sets must be non-null). Direct cycles may remain. -}
collaps :: Ord a => [Set.Set a] -> Rel a -> Rel a
collaps = delSet . Set.unions . List.map Set.deleteMin

setToMap :: Ord a => Set.Set a -> Map.Map a ()
setToMap s = Map.fromDistinctAscList $
             List.map (\ a -> (a, ())) $ Set.toList s

{- | transitive reduction (minimal relation with the same transitive closure)
     of a transitively closed DAG (i.e. without cycles)! -}
transReduce :: Ord a => Rel a -> Rel a
transReduce (Rel m) = Rel $ rmNull $
-- keep all (i, j) in rel for which no c with (i, c) and (c, j) in rel
    Map.mapWithKey ( \ i s -> let d = setToMap $ Set.delete i s in
        Set.filter ( \ j ->
            Map.null $ Map.filter (Set.member j)
                $ Map.intersection m $ Map.delete j d) s) m

-- | convert a list of ordered pairs to a relation
fromList :: Ord a => [(a, a)] -> Rel a
fromList = foldr (uncurry insert) empty

-- | convert a relation to a list of ordered pairs
toList :: Rel a -> [(a, a)]
toList (Rel m) = concatMap (\ (a , bs) -> List.map ( \ b -> (a, b) )
                            (Set.toList bs)) $ Map.toList m

instance (Show a, Ord a) => Show (Rel a) where
    show = show . Set.fromDistinctAscList . toList

-- | Insert into a set of values
setInsert :: (Ord k, Ord a) => k -> a -> Map.Map k (Set.Set a)
          -> Map.Map k (Set.Set a)
setInsert kx x t =
    Map.insert kx (Set.insert x $ Map.findWithDefault Set.empty kx t) t

-- | the image of a map
image :: (Ord k, Ord a) => Map.Map k a -> Set.Set k -> Set.Set a
image f s =
  Set.fold ins Set.empty s
  where ins x = case Map.lookup x f of
                 Nothing -> id
                 Just y -> Set.insert y

-- | map the values of a relation
map :: (Ord a, Ord b) => (a -> b) -> Rel a -> Rel b
map f (Rel m) = Rel $ Map.foldWithKey
    ( \ a v -> Map.insertWith Set.union (f a) $ Set.map f v) Map.empty m

-- | Restriction of a relation under a set
restrict :: Ord a => Rel a -> Set.Set a -> Rel a
restrict r s = delSet (nodes r Set.\\ s) r

-- | restrict to elements not in the input set
delSet :: Ord a => Set.Set a -> Rel a -> Rel a
delSet s (Rel m) = Rel $ rmNull (Map.map (Set.\\ s) m) Map.\\ setToMap s

-- | convert a relation to a set of ordered pairs
toSet :: (Ord a) => Rel a -> Set.Set (a, a)
toSet = Set.fromDistinctAscList . toList

-- | convert a set of ordered pairs to a relation
fromSet :: (Ord a) => Set.Set (a, a) -> Rel a
fromSet s = fromAscList $ Set.toList s

-- | convert a sorted list of ordered pairs to a relation
fromAscList :: (Ord a) => [(a, a)] -> Rel a
fromAscList = Rel . Map.fromDistinctAscList
                  . List.map ( \ l -> (fst (head l),
                                  Set.fromDistinctAscList $ List.map snd l))
                        . List.groupBy ( \ (a, _) (b, _) -> a == b)

-- | all nodes of the edges
nodes :: Ord a => Rel a -> Set.Set a
nodes (Rel m) = Set.union (Map.keysSet m) $ elemsSet m

elemsSet :: Ord a => Map.Map a (Set.Set a) -> Set.Set a
elemsSet = Set.unions . Map.elems

{- | Construct a precedence map from a closed relation. Indices range
   between 1 and the second value that is output. -}
toPrecMap :: Ord a =>  Rel a -> (Map.Map a Int, Int)
toPrecMap r = foldl ( \ (m1, c) s -> let n = c + 1 in
                    (Set.fold ( \ i -> Map.insert i n) m1 s, n))
                 (Map.empty, 0) $ topSort r

topSortDAG :: Ord a => Rel a -> [Set.Set a]
topSortDAG r@(Rel m) = if Map.null m then [] else
    let es = elemsSet m
        ml = Map.keysSet m Set.\\ es -- most left
        Rel m2 = delSet ml r
        rs = es Set.\\ Map.keysSet m2 -- re-insert loose ends
    in ml : topSortDAG (Rel $ Set.fold (flip Map.insert Set.empty) m2 rs)

-- | topologically sort a closed relation (ignore isolated cycles)
topSort :: Ord a => Rel a -> [Set.Set a]
topSort r = let cs = sccOfClosure r in
      List.map (expandCycle cs) $ topSortDAG $ irreflex $ collaps cs r

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
mostRightOfCollapsed r@(Rel m) = if Map.null m then Set.empty
    else let Rel im = irreflex r
             mr = elemsSet im Set.\\ Map.keysSet im
         in if Set.null mr then Map.keysSet $ Map.filterWithKey (\ k v ->
                                           Set.singleton k == v) m
            else mr

{--------------------------------------------------------------------
  MostRight (Added by K.L.)
--------------------------------------------------------------------}
{- |
find s such that x in s => forall y . yRx or not yRx and not xRy

 * precondition: (transClosure r == r)

 * strongly connected components (cycles) are treated as a compound node
-}

mostRight :: (Ord a) => Rel a -> (Set.Set a)
mostRight r = let
    cs = sccOfClosure r
    in expandCycle cs (mostRightOfCollapsed $ collaps cs r)

{--------------------------------------------------------------------
  intransitive kernel (Added by K.L.)
--------------------------------------------------------------------}
-- |
-- intransitive kernel of a reflexive and transitive closure
--
-- * precondition: (transClosure r == r)
--
-- * cycles are uniquely represented (according to Ord)
intransKernel :: Ord a => Rel a -> Rel a
intransKernel r =
    let cs = sccOfClosure r
    in foldr addCycle (transReduce $ collaps cs r) cs

-- add a cycle given by a set in the collapsed node
addCycle :: Ord a => Set.Set a -> Rel a -> Rel a
addCycle c r = if Set.null c then error "Common.Lib.Rel.addCycle" else
    let (a, b) = Set.deleteFindMin c
        (m, d) = Set.deleteFindMax c
    in insert m a $ foldr ( \ (x, y) -> insert x y) (delete a a r) $
       zip (Set.toList d) (Set.toList b)

{--------------------------------------------------------------------
  common transitive left element of two elements (Added by K.L.)
--------------------------------------------------------------------}
-- | calculates if two given elements have a common left element
--
-- * if one of the arguments is not present False is returned
haveCommonLeftElem :: (Ord a) => a -> a -> Rel a -> Bool
haveCommonLeftElem t1 t2 =
    Map.fold(\ e rs -> rs || (t1 `Set.member` e &&
                              t2 `Set.member` e)) False . toMap

-- | partitions a set into a list of disjoint non-empty subsets
-- determined by the given function as equivalence classes
partSet :: (Ord a) => (a -> a -> Bool) -> Set.Set a -> [(Set.Set a)]
partSet f s = if Set.null s then [] else
              let (x, s') = Set.deleteFindMin s
                  (ds, es) = List.partition (Set.null . Set.filter (f x))
                             $ partSet f s'
              in Set.insert x (Set.unions es) : ds

-- | flattens a list of non-empty sets and uses the minimal element of
-- each set to represent the set
flatSet :: (Ord a) => [Set.Set a] -> Set.Set a
flatSet = Set.fromList . List.map (\s -> if Set.null s
                         then error "Common.Lib.Rel.flatSet"
                         else Set.findMin s)

-- | checks if a given relation is locally filtered
--
-- precondition: the relation must already be closed by transitive closure
locallyFiltered :: (Ord a) => Rel a -> Bool
locallyFiltered rel = (check . flatSet . partSet iso . mostRight) rel
    where iso x y = member x y rel && member y x rel
          check s = Set.null s ||
                  Set.fold (\y rs -> rs &&
                                     not (haveCommonLeftElem x y rel)) True s'
                  && check s'
              where (x,s') = Set.deleteFindMin s
