
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Till Mossakowski, Klaus Lüttich and Uni Bremen 2003
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
                       succs, predecessors, irreflex, sccOfClosure,
                       transClosure, fromList, toList, image,
		       intransKernel,mostRight,rmSym,symmetricSets,
		       rmReflex,
                       restrict, toSet, fromSet, topSort, nodes,
                       transpose, connComp, collaps, transReduce) where

import Debug.Trace

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Data.List(groupBy)

import Data.Maybe (catMaybes)
import QuickCheck

data Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Eq
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

-- | delete an ordered pair
delete :: Ord a => a -> a -> Rel a -> Rel a
delete a b r
    | member a b r = let s = Set.delete b (Map.find a (toMap r)) 
                     in if Set.isEmpty s 
			then Rel $ Map.delete a $ toMap r 
			else Rel $ Map.insert a s $ toMap r
    | otherwise    = r

-- | test for an (previously inserted) ordered pair
member :: Ord a => a -> a -> Rel a -> Bool
member a b r = Set.member b $ succs r a

{--------------------------------------------------------------------
  SymMember (Added by K.L.)
--------------------------------------------------------------------}
-- | test if elements are related in both directions
symMember :: Ord a => a -> a -> Rel a -> Bool
symMember a b r = member a b r && member b a r

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

{--------------------------------------------------------------------
  SymMember (Added by K.L.)
--------------------------------------------------------------------}
-- | test for proper transitive membership
propTransMember :: Ord a => a -> a -> Rel a -> Bool
propTransMember a b r = not (member a b r) && path a b r

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

-- | compute strongly connected components for a transitively closed relation 
sccOfClosure :: Ord a => Rel a -> Map.Map a (Set.Set a)
sccOfClosure r@(Rel m) = 
        fst $ Map.foldWithKey
               ( \ k v (m1, s) -> 
                let s1 = Set.delete k s in
                if Set.member k v then
                  if Set.member k s then (m1, s1) 
                     else let s2 = preds r k v in
                           (Map.insert k s2 m1, Set.union s1 
                            $ Set.filter (> k) s2)
                 else (m1, s1)) (Map.empty, Set.empty) m

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


{--------------------------------------------------------------------
  MostRight (Added by K.L.)
--------------------------------------------------------------------}
{- | 
find s such that forall y . yRx and x in s (only the maximal element
of symmetric most right elements is inlcuded in s; all elements in s
are not symmetric)

  * precondition: (transClosure r == r)

 * only the greatest element of symmetric elements is shown 
   according to Ord

 * Cyclic relations have no toplevel element!
-}
mostRight :: (Ord a) => Rel a -> (Set.Set a)
mostRight r = 
    let rmp = toMap $ rmSym $ rmReflex r
    in (Set.unions $ Map.elems rmp) Set.\\ 
	    (Set.fromDistinctAscList $ Map.keys rmp)

{--------------------------------------------------------------------
  symmetricSets (Added by K.L.)
--------------------------------------------------------------------}
-- | symmetricSets calculates a Set of Sets of Symmetric elements
--
-- * precondition: (transClosure r == r)
symmetricSets :: (Ord a) => Rel a -> Set.Set (Set.Set a)
symmetricSets rel = 
    fst $ Map.foldWithKey  
	   (\k e (s,seen) -> 
	      if not (Set.isEmpty seen) && 
	         k == Set.findMin seen 
	      then (s,seen) 
	      else (let sym = Set.fold (\ e1 s1 -> 
					      if member e1 k rel
					      then Set.insert k $ 
					           Set.insert e1 s1
					      else s1) Set.empty  e 
		    in if Set.isEmpty sym 
		       then s 
		       else Set.insert sym s
		   ,Set.insert k seen `Set.union` e))
	   (Set.empty,Set.empty)  $ 
		      toMap $ rmReflex rel 

symmetricMap :: (Ord a) => Rel a -> Map.Map a (Set.Set a) 
symmetricMap = Set.fold (\s mp -> 
			       Set.fold (\k mp1 -> 
					   Map.insert k s mp1) mp s)
		            Map.empty . symmetricSets
		  

{-
-- slower version of symmetricSets fold over pairs
symmetricSetsFP :: (Ord a) => Rel a -> Set.Set (Set.Set a)
symmetricSetsFP rel = 
    let rl =  Map.keys $ toMap rel
	tr_rel = transClosure rel
	sym (x,y) m = if symMember x y tr_rel 
		       then Map.setInsert y x $ 
			    Map.setInsert x y m
		       else m
    in Map.foldWithKey (\k e -> Set.insert (Set.insert k e)) 
                       Set.empty $ 
       foldr sym Map.empty [(x,y) | x <- rl, y <- rl, x<y]    
-}


{--------------------------------------------------------------------
  remove reflexive (Added by K.L.)
--------------------------------------------------------------------}
-- | remove reflexive relations
rmReflex :: (Ord a) => Rel a -> Rel a
rmReflex = Rel . Map.mapWithKey Set.delete . toMap

{--------------------------------------------------------------------
  intransitive kernel (Added by K.L.)
--------------------------------------------------------------------}
-- |
-- intransitive kernel of a reflexive and transitive closure
--
-- * every left element is related to all symmetric right elements if (transClosure r == r)
--
-- * Warning: all reflexive relations are removed!!
intransKernel :: (Show a ,Ord a) => Rel a -> Rel a
intransKernel r = 
    let rmap = toMap $ rmReflex $ rmSym r
	insDirR k set m = Map.insert k (dirRight set) m
	dirRight set = set Set.\\ transRight set
	transRight =  Set.unions . map lkup . Set.toList
	lkup = (\ e -> maybe Set.empty id (Map.lookup e rmap))
	addSym sm mp = 	      
	    let checkAllSym m = 
		    Set.fold (\k cm -> if Map.member k cm 
                                         then cm 
                                         else Map.insert k 
                                              (Map.find k sm) cm) 
		               m $ Set.unions $ Map.elems sm
	    in Rel $ checkAllSym 
		   $ Map.mapWithKey 
			 (\ k s -> Set.delete k $
			           Set.unions (s:catMaybes (concatMap  
				        (\x-> let ms = Map.lookup x sm
                                              in maybe ([ms]) 
                                                    (\ _ -> [ms,
							     Map.lookup x 
							       mp]) 
					            ms) 
                                            (k:Set.toList s)))) 
		   $ mp 
    in addSym (symmetricMap r) $ 
       Map.foldWithKey insDirR Map.empty rmap

{--------------------------------------------------------------------
  remove symmetric relations (Added by K.L.)
--------------------------------------------------------------------}
-- extend to
-- aRb /\ bRa /\ bRc /\ aRd ~~> aRb /\ bRc /\ aRd /\ aRc /\ bRd with a<b /\ a/=b/=c/=d
-- | remove symmetric relations aRb and bRa ~~> aRb with a < b
--
-- * precondition: (transClosure r == r)
rmSym :: (Ord a) => Rel a -> Rel a
rmSym rel =
          let rl = Map.keys (toMap rel) 
	      sym (x,y) r1 = if symMember x y rel 
			      then delete y x r1
			      else r1
          in foldr sym rel [(x,y) | x <- rl, y <- rl, x<y]    

{--------------------------------------------------------------------
  common transitive left element of two elements (Added by K.L.)
--------------------------------------------------------------------}
-- | calculates if two given elements have a common left element
--
-- * precondition: (transClosure r == r)
--
-- * if one of the arguments is not present False is returned
haveCommonLeftElem :: (Ord a) => a -> a -> Rel a -> Bool
haveCommonLeftElem t1 t2 =
    Map.foldWithKey (\ k e rs -> rs || 
		                (t1 `Set.member` e && 
				 t2 `Set.member` e)) False . toMap

{- slower variant of rmSym
rmSymMF :: (Show a, Ord a) => Rel a -> Rel a
rmSymMF rel = 
   Map.foldWithKey  
	   (\k e r ->  Set.fold (\ e1 r1 -> 
				     if k < e1
				     then delete e1 k r1
				     else r1) r e) 
	  rel $ toMap $ rel 
-}

{-
    Map.mapAccumWithKey  
	   (\ (seen,del) k e -> 
	      if k `Set.member` seen 
	      then ((seen,del),e) 
	      else let sym = Set.fold (\ e1 s1 -> 
					      if e1 < k
					      then Set.delete e1 s1
					      else s1) Set.empty  e 
		       seen' = Set.insert k seen `Set.union` e
		    in if Set.isEmpty sym 
		       then ((seen',k:del),sym) 
		       else ((seen',del),sym)
		   )
	   (Set.empty,[])  $ 
		      toMap $ transClosure $ rel 
-}

instance Arbitrary (Rel Int) where
    arbitrary = do l <- arbitrary
		   l1 <- arbitrary
		   l2 <- arbitrary
		   let r = fromList $ filter (\ (x,y) -> x/=y) (l++l1++l2)
		       keys = Map.keys $ toMap r
                   x <- choose (0,length keys-1)
		   y <- choose (0,length keys-3)
		   z <- choose (0,length keys-1)
		   x1 <- choose (0,length keys-2)
		   y1 <- choose (0,length keys-1)
		   let r' = 
			insert x1 y1 $
			insert y1 x1 $
			insert x y $
			insert x z $
			insert z y $
			insert y x $ r
		   return r'



prop_transReduce_transClosure = prp_transClosure transReduce
prop_intransKernel_transClosure = prp_transClosure intransKernel

prp_transClosure intrKern r =
    (Set.size (mostRight r) <= 3 && 
     Set.size (symmetricSets r) > 1 &&
     length (Map.keys $ toMap r) > 6 )  ==>
       ((Set.size $ toSet $ rmReflex r) < 10) `trivial`
        collect (length (Map.keys $ toMap r))
		 (transClosure (rmReflex r) == 
		  transClosure (intrKern $ transClosure r))
    where rel = r::(Rel Int)

tr = transClosure test1
 
test1 = fromList (zip [(1::Int)..7] [2..8] ++ 
		 [(2,1),(12,11),(4,12),(12,13),(13,12),
		 (11,14),(14,11),(-1,14),(14,-1),(100,1),(2,100)])

test2 = fromList [(1,2::Int),(2,3),(3,2),(3,5),(3,4),(1,4),(4,5),
		  (4,6),(5,6),(6,7),(6,8),(7,9),(8,9)]

test3 = delete 100 1 (test1 `union` fromList (zip [7..100] [8..101]))

test4 = test3 `union` fromList (zip [100..300] [101..301])

test5 = test4 `union` (test2 `union` fromList (zip [301..500] [302,501]))

test6 = fromList [(2,1::Int),(3,1),(5,2),(5,4),(4,5),(6,3),(7,3),(8,5),(8,6),(8,7),(9,8),(8,9),(9,5),(2,-1),(-11,-10),(-12,-10),(-1,-3)]

test7 = fromList [(2,1),(3,1),(4,2),(5,2),(6,3),(7,6),(8,6::Int),(-7,7),(7,-7)]

myQuick = Config
  { configMaxTest = 100
  , configMaxFail = 2000
  , configSize    = (+ 3) . (`div` 2)
  , configEvery   = \n args -> let s = show n in s ++ [ '\b' | _ <- s ]
  }