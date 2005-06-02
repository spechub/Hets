{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003-2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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

The functions 'image', 'keysSet' and 'setInsert' are utility functions
for plain maps involving sets.

-}

module Common.Lib.Rel (Rel(), empty, Common.Lib.Rel.null, 
                       insert, member, toMap, Common.Lib.Rel.map, 
                       union , isSubrelOf, difference, path, delete,
                       succs, predecessors, irreflex, sccOfClosure,
                       transClosure, fromList, toList, image,
                       intransKernel, mostRight,
                       restrict, toSet, fromSet, topSort, nodes,
                       transpose, transReduce, setInsert, keysSet,
                       haveCommonLeftElem) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Data.List as List

data Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Eq
-- the invariant is that set values are never empty

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
insert a b (Rel m) = Rel $ Map.insert a 
    (Set.insert b $ Map.findWithDefault Set.empty a m) m  

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
predecessors r@(Rel m) a = preds r a $ keysSet m

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
collaps cs = delSet $ Set.unions $ List.map Set.deleteMin cs

{- | transitive reduction (minimal relation with the same transitive closure)
     of a DAG. -}
transReduce :: Ord a => Rel a -> Rel a
transReduce rel@(Rel m) =
    Map.foldWithKey ( \ i ->
               flip $ Set.fold ( \ j ->
               if covers i j rel then 
                  insert i j else id)) empty m
    where
    -- (a, b) in r but no c with (a, c) and (c, b) in r
    covers :: Ord a => a -> a -> Rel a -> Bool
    covers a b r = Set.null $ Set.filter ( \ c -> path c b r) 
                       (Set.delete a $ Set.delete b $ reachable r a)  

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
delSet s (Rel m) = Rel $ Map.filterWithKey 
    ( \ a _ -> not $ Set.member a s) $ rmNull $ Map.map (Set.\\ s) m 

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
nodes (Rel m) = Set.union (keysSet m) $ elemsSet m

-- | The set of all keys of the map
keysSet :: Ord a => Map.Map a b -> Set.Set a
keysSet = Set.fromDistinctAscList . Map.keys

elemsSet :: Ord a => Map.Map a (Set.Set a) -> Set.Set a
elemsSet = Set.unions . Map.elems

topSortDAG :: Ord a => Rel a -> [Set.Set a]
topSortDAG r@(Rel m) = if Map.null m then [] else
    let ml = keysSet m Set.\\ elemsSet m -- most left
    in ml : topSortDAG (delSet ml r)

-- | topologically sort a closed relation (ignore isolated cycles)
topSort :: Ord a => Rel a -> [Set.Set a]
topSort r = let cs = sccOfClosure r in
      List.map (expandCycle cs) $ topSortDAG $ irreflex $ collaps cs r 

-- | find the cycle and add it to the result set
expandCycle :: Ord a => [Set.Set a] -> Set.Set a -> Set.Set a
expandCycle [] s = s
expandCycle (c : r) s = if Set.null c then error "expandCycle" else
    let (a, b) = Set.deleteFindMin c in
    if Set.member a s then Set.union b s else expandCycle r s

{- | gets the most right elements of the irreflexive relation, 
     unless no hierarchy is left then isolated nodes are output -}
mostRightOfCollapsed :: Ord a => Rel a -> Set.Set a
mostRightOfCollapsed r@(Rel m) = if Map.null m then Set.empty
    else let Rel im = irreflex r 
             mr = elemsSet im Set.\\ keysSet im
         in if Set.null mr then keysSet $ Map.filterWithKey (\ k v -> 
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
addCycle c r = if Set.null c then error "addCycle" else
    let (a, b) = Set.deleteFindMin c 
        (m, d) = Set.deleteFindMax c 
    in insert m a $ foldr ( \ (x, y) -> insert x y) (delete a a r) $ 
       zip (Set.toAscList d) (Set.toAscList b) 


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
