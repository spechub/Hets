
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
An alternative view is that of a directed Graph without isolated nodes.

'Rel' replaces a directed graph with unique node labels (Ord a) and
unlabelled edges (without multiplicity higher than one).

Usage: start with an 'empty' relation, 'insert' edges, and test for
an edge 'member' (before or after calling 'transClosure'). 

It is possible to insert self edges or bigger cycles.

Checking for a 'path' corresponds to checking for a member in the 
transitive closure. A further 'insert', however,
may destroy the closedness property of a relation.

-}

module Common.Lib.Rel (Rel(), empty, isEmpty, insert, member, toMap,
                       union , subset, difference, path,
                       transClosure, fromList, toList, image,
                       restrict, toSet, fromSet, topSort, 
                       transpose, connComp) where

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

-- | test for 'member' or transitive membership
path :: Ord a => a -> a -> Rel a -> Bool
path a b r = Set.member b $ reachable r a

-- | compute transitive closure (make all transitive members direct members)
transClosure :: Ord a => Rel a -> Rel a
transClosure r = Rel $ Map.mapWithKey ( \ k _ ->  reachable r k) $ toMap r

{- adapted from D. King, J. Launchbury 95: 
   Structuring depth-first search algorithms in Haskell.
   (using Common.Lib.State and foldM makes it longer

-}

data Tree a = Node a [Tree a] deriving Show

-- | get dfs tree rooted at node
dfsT :: Ord a => Rel a -> Set.Set a -> a -> (Set.Set a, Tree a)
dfsT r s v = let (t, ts) = dfsF r (Set.insert v s) $ Set.toList $ getDAdjs r v 
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
dff r = dfs r $ Map.keys $ toMap r

-- | get reverse relation
transpose :: Ord a => Rel a -> Rel a 
transpose = fromList . map (\ (a, b) -> (b, a)) . toList 

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

reachable :: Ord a => Rel a -> a -> Set.Set a 
reachable r = flatF . dfs r . Set.toList . getDAdjs r

{- | Connected components as a mapping from a minimal representative
     to all other reachable nodes. Transposing the result allows
     replacing nodes by a unique representatives. -}
connComp :: Ord a => Rel a -> Rel a
connComp r = Rel $ foldr (\ t m -> 
                    let s = flatT t in 
                    Map.insert (Set.findMin s) s m) Map.empty $ scc r

{-
-- | transitive reduction (minimal relation with the same transitive closure)
transReduce :: Ord a => Rel a -> Rel a
-}

-- | convert a list of ordered pairs to a relation 
fromList :: Ord a => [(a, a)] -> Rel a
fromList = foldr (\ (a, b) -> insert a b) empty

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
fromSet = Set.fold (\ (a, b) -> insert a b) empty

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
           if r == cl then Nothing -- no cycle there 
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
