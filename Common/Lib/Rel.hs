
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2003
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

Some parts are adapted from D. King, J. Launchbury 95: 
   Structuring depth-first search algorithms in Haskell.
-}

module Common.Lib.Rel (Rel(), empty, isEmpty, insert, member, toMap,
                       union , subset, difference, path,
                       succs, predecessors, irreflex,
                       transClosure, fromList, toList, image,
                       restrict, toSet, fromSet, topSort, nodes,
                       transpose, connComp, collaps, transReduce) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Data.List(groupBy)

data Rel a = Rel {toMap :: Map.Map a (Set.Set a)} deriving Eq
-- the invariant is that set values are never empty

-- | the empty relation
empty :: Rel a
empty = Rel Map.empty

-- | test for 'empty'
isEmpty :: Rel a -> Bool
isEmpty (Rel m) = Map.isEmpty m

-- | difference of two relations
difference :: Ord a => Rel a -> Rel a -> Rel a
difference a b = fromSet (toSet a Set.\\ toSet b)

-- | union of two relations
union :: Ord a => Rel a -> Rel a -> Rel a
union a b = fromSet $ Set.union (toSet a) $ toSet b

-- | is the first relation a subset of the second
subset :: Ord a => Rel a -> Rel a -> Bool
subset a b = Set.subset (toSet a) $ toSet b

-- | insert an ordered pair
insert :: Ord a => a -> a -> Rel a -> Rel a
insert a b (Rel m) = Rel $ Map.setInsert a b m 

-- | test for an (previously inserted) ordered pair
member :: Ord a => a -> a -> Rel a -> Bool
member a b r = Set.member b $ succs r a

-- | get direct successors
succs :: Ord a => Rel a -> a -> Set.Set a
succs (Rel m) a = Map.findWithDefault Set.empty a m

-- | predecessors in the given set of a node 
preds :: Ord a => Rel a -> a -> Set.Set a -> Set.Set a
preds r a = Set.filter ( \ s -> member s a r)

-- | get direct predecessors inefficiently
predecessors :: Ord a => Rel a -> a -> Set.Set a
predecessors r@(Rel m) a = preds r a $ keySet m

-- | test for 'member' or transitive membership (non-empty path)
path :: Ord a => a -> a -> Rel a -> Bool
path a b r = Set.member b $ reachable r a

-- | compute transitive closure (make all transitive members direct members)
transClosure :: Ord a => Rel a -> Rel a
transClosure r@(Rel m) = Rel $ Map.mapWithKey ( \ k _ -> reachable r k) m

data Tree a = Node a [Tree a] deriving Show

-- | get dfs tree rooted at node
dfsT :: Ord a => Rel a -> Set.Set a -> a -> (Set.Set a, Tree a)
dfsT r s v = let (t, ts) = dfsF r (Set.insert v s) $ Set.toList $ succs r v 
                 in (t, Node v ts)

-- | get dfs forest for a list of nodes
dfsF :: Ord a => Rel a -> Set.Set a -> [a] -> (Set.Set a, [Tree a])
dfsF r s l = case l of
    [] -> (s, [])
    x : xs -> if Set.member x s then dfsF r s xs else
        let (t, a) = dfsT r s x
            (u, ts) = dfsF r t xs in (u, a : ts)

-- | get dfs forest of a relation 
dfs :: Ord a => Rel a -> [a] -> [Tree a]
dfs r = snd . dfsF r Set.empty 

-- | get dfs forest of a relation 
dff :: Ord a => Rel a -> [Tree a]
dff r@(Rel m) = dfs r $ Map.keys m

-- | get reverse relation
transpose :: Ord a => Rel a -> Rel a 
transpose = fromList . map ( \ (a, b) -> (b, a)) . toList

flatT :: Ord a => Tree a -> Set.Set a
flatT (Node v ts) = Set.insert v $ flatF ts

flatF :: Ord a => [Tree a] -> Set.Set a
flatF = Set.unions . map flatT

postOrdT :: Tree a -> [a] -> [a]
postOrdT (Node v ts) = postOrdF ts . (v:) 

postOrdF :: [Tree a] -> [a] -> [a]
postOrdF = foldr (.) id . map postOrdT

postOrd :: Ord a => Rel a -> [a]
postOrd r = postOrdF (dff r) []

scc :: Ord a => Rel a -> [Tree a]
scc r = dfs r $ reverse $ postOrd $ transpose r

-- | reachable nodes excluding the start node if there is no cycle
reachable :: Ord a => Rel a -> a -> Set.Set a 
reachable r = flatF . dfs r . Set.toList . succs r

-- | make relation irreflexive 
irreflex :: Ord a => Rel a -> Rel a
irreflex (Rel m) = Rel $ Map.foldWithKey ( \ k s -> 
           let r = Set.delete k s in 
           if Set.isEmpty r then id else
              Map.insert k r) Map.empty m 

{- | Connected components as a mapping to a minimal representative 
   and the reverse mapping -} 
connComp :: Ord a => Rel a -> (Map.Map a a, Map.Map a (Set.Set a))
connComp r = foldr (\ t (m1, m2) -> 
                    let s = flatT t 
                        m = Set.findMin s 
                    in (Set.fold (flip Map.insert m) m1 s,
                        Map.insert m s m2))
                    (Map.empty, Map.empty) $ scc r

-- | collaps strongly connected components to its minimal representative
collaps :: Ord a => Map.Map a a -> Rel a -> Rel a
collaps c = image (\ e -> Map.findWithDefault e e c)

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
    covers a b r = Set.all ( \ c -> not $ path c b r) 
                       (Set.delete a $ Set.delete b $ reachable r a)  

-- | convert a list of ordered pairs to a relation 
fromList :: Ord a => [(a, a)] -> Rel a
fromList = foldr (uncurry insert) empty

-- | convert a relation to a list of ordered pairs
toList :: Rel a -> [(a, a)]
toList (Rel m) = concatMap (\ (a , bs) -> map ( \ b -> (a, b) ) 
                            (Set.toList bs)) $ Map.toList m

instance (Show a, Ord a) => Show (Rel a) where
    show = show . Set.fromDistinctAscList . toList

{--------------------------------------------------------------------
  Image (Added by T.M.) (implementation changed by C.M.)
--------------------------------------------------------------------}
-- | Image of a relation under a function
image :: (Ord a, Ord b) => (a -> b) -> Rel a -> Rel b
image f (Rel m) = Rel $ Map.foldWithKey 
    ( \ a v -> Map.insertWith Set.union (f a) $ Set.image f v) Map.empty m 

{--------------------------------------------------------------------
  Restriction (Added by T.M.) 
--------------------------------------------------------------------}
-- | Restriction of a relation under a set
restrict :: Ord a => Rel a -> Set.Set a -> Rel a
restrict (Rel m) s = Rel $ Map.foldWithKey 
    ( \ a v -> if Set.member a s then
                   let r = Set.intersection v s in
                   if Set.isEmpty r then id else Map.insert a r
               else id) Map.empty m 

{--------------------------------------------------------------------
 Conversion from/to sets (Added by T.M.) (implementation changed by C.M.)
--------------------------------------------------------------------}
-- | convert a relation to a set of ordered pairs
toSet :: (Ord a) => Rel a -> Set.Set (a, a)
toSet = Set.fromDistinctAscList . toList

-- | convert a set of ordered pairs to a relation 
fromSet :: (Ord a) => Set.Set (a, a) -> Rel a
fromSet s = fromAscList $ Set.toList s

-- | convert a sorted list of ordered pairs to a relation 
fromAscList :: (Ord a) => [(a, a)] -> Rel a
fromAscList = Rel . Map.fromDistinctAscList 
                  . map ( \ l -> (fst (head l), 
                                  Set.fromDistinctAscList $ map snd l))
                        . groupBy ( \ (a, _) (b, _) -> a == b)

-- | all nodes of the edges
nodes :: Ord a => Rel a -> Set.Set a
nodes (Rel m) = Set.union (keySet m) $ elemSet m

keySet :: Ord a => Map.Map a b -> Set.Set a
keySet = Set.fromDistinctAscList . Map.keys

elemSet :: Ord a => Map.Map a (Set.Set a) -> Set.Set a
elemSet = Set.unions . Map.elems

-- | topological sort a relation (more efficient for a closed relation)
topSort :: Ord a => Rel a -> [Set.Set a]
topSort r@(Rel m) = 
    if isEmpty r then []
    else let ms = keySet m Set.\\ elemSet m in 
        if Set.isEmpty ms then case removeCycle r of 
           Nothing -> topSort (transClosure r)
           Just (a, cyc, restRel) ->
               map ( \ s -> if Set.member a s then 
                     Set.union s cyc else s) $ topSort restRel
        else let (lowM, rest) = 
                     Map.partitionWithKey (\ k _ -> Set.member k ms) m
                 -- no not forget loose ends 
                 ls = elemSet lowM Set.\\ keySet rest in 
                 -- put them as low as possible
            ms : (topSort $ Rel $ Set.fold ( \ i -> 
                      Map.insert i Set.empty) rest ls)

-- | try to remove a cycle
removeCycle :: Ord a => Rel a -> Maybe (a, Set.Set a, Rel a)
removeCycle r@(Rel m) = 
    let cycles = Map.filterWithKey Set.member m in
        if Map.isEmpty cycles then Nothing
           else let (a, os) = Map.findMin cycles
                    cs = preds r a os
                    m1 = Map.foldWithKey 
                         ( \ k v -> let i = v Set.\\ cs 
                                    in if Set.member k cs 
                                       then Map.insertWith Set.union a i
                                       else Map.insert k 
                                            (if Set.size v > Set.size i 
                                             then Set.insert a i else i))
                         Map.empty m
                    in Just (a, Set.delete a cs, Rel m1)

{- The result is a representative "a", the cycle "cs", i.e. all other
elements that are represented by "a" and the remaining relation with
all elements from "cs" replaced by "a" and without the cycle "(a,a)"
-}
