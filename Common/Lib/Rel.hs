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

-}

module Common.Lib.Rel (Rel(), empty, Common.Lib.Rel.null, 
                       insert, member, toMap, Common.Lib.Rel.map, 
                       union , isSubrelOf, difference, path, delete,
                       succs, predecessors, irreflex, sccOfClosure,
                       transClosure, fromList, toList, image,
                       intransKernel, mostRight, rmSym, symmetricSets,
                       restrict, toSet, fromSet, topSort, nodes,
                       transpose, collaps, transReduce, setInsert,
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

{--------------------------------------------------------------------
  SymMember (Added by K.L.)
--------------------------------------------------------------------}
-- | test if elements are related in both directions
symMember :: Ord a => a -> a -> Rel a -> Bool
symMember a b r = member a b r && member b a r

-- | get direct successors
succs :: Ord a => Rel a -> a -> Set.Set a
succs (Rel m) a = Map.findWithDefault Set.empty a m

reachable :: Ord a => Rel a -> a -> Set.Set a
reachable r a = Set.fold reach Set.empty $ succs r a where
    reach e s = if Set.member e s then s 
                    else Set.fold reach (Set.insert e s) $ succs r e

-- | predecessors of one node in the given set of a nodes 
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

-- | get reverse relation
transpose :: Ord a => Rel a -> Rel a 
transpose = fromList . List.map ( \ (a, b) -> (b, a)) . toList

-- | make relation irreflexive 
irreflex :: Ord a => Rel a -> Rel a
irreflex (Rel m) = Rel $ Map.foldWithKey ( \ k s -> 
           let r = Set.delete k s in 
           if Set.null r then id else
              Map.insert k r) Map.empty m 

-- | compute strongly connected components for a transitively closed relation 
sccOfClosure :: Ord a => Rel a -> [Set.Set a]
sccOfClosure r@(Rel m) = 
        if Map.null m then []
        else let ((k, v), p) = Map.deleteFindMin m in
             if Set.member k v then
                let c = preds r k v in
                c : sccOfClosure (Rel $ Set.fold Map.delete p c)
             else sccOfClosure (Rel p) 

{- | collaps strongly connected components to its minimal representative
     (input must be transitively closed) -}
collaps :: Ord a => Rel a -> Rel a
collaps r = let
    toCollapsMap l = case l of 
        [] -> Map.empty
        x : t -> let (m, s) = Set.deleteFindMin x in
                     Set.fold ( \ e -> Map.insert e m) (toCollapsMap t) s 
    in Common.Lib.Rel.map 
           (\ e -> Map.findWithDefault e e $ toCollapsMap $ sccOfClosure r) r

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

{--------------------------------------------------------------------
  Image (Added by T.M.) (implementation changed by C.M.)
--------------------------------------------------------------------}

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

{--------------------------------------------------------------------
  Restriction (Added by T.M.) 
--------------------------------------------------------------------}
-- | Restriction of a relation under a set
restrict :: Ord a => Rel a -> Set.Set a -> Rel a
restrict (Rel m) s = Rel $ Map.foldWithKey 
    ( \ a v -> if Set.member a s then
                   let r = Set.intersection v s in
                   if Set.null r then id else Map.insert a r
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
                  . List.map ( \ l -> (fst (head l), 
                                  Set.fromDistinctAscList $ List.map snd l))
                        . List.groupBy ( \ (a, _) (b, _) -> a == b)

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
    if Map.null m then []
    else let ms = keySet m Set.\\ elemSet m in 
        if Set.null ms then case removeCycle r of 
           Nothing -> topSort (transClosure r)
           Just (a, cyc, restRel) ->
               List.map ( \ s -> if Set.member a s then 
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
        if Map.null cycles then Nothing
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
              if not (Set.null seen) && 
                 k == Set.findMin seen 
              then (s,seen) 
              else (let sym = Set.fold (\ e1 s1 -> 
                                              if member e1 k rel
                                              then Set.insert k $ 
                                                   Set.insert e1 s1
                                              else s1) Set.empty  e 
                    in if Set.null sym 
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
                  
{--------------------------------------------------------------------
  remove reflexive (Added by K.L.)
--------------------------------------------------------------------}
-- | remove reflexive relations
-- Warning: this function violates the empty set condition
rmReflex :: (Ord a) => Rel a -> Rel a
rmReflex = Rel . Map.mapWithKey Set.delete . toMap

{--------------------------------------------------------------------
  intransitive kernel (Added by K.L.)
--------------------------------------------------------------------}
-- |
-- intransitive kernel of a reflexive and transitive closure
--
-- * only the lowest (according to Ord) left element is related to all symmetric right elements if (transClosure r == r)
--
-- * Warning: all reflexive relations are removed!!
intransKernel :: (Show a ,Ord a) => Rel a -> Rel a
intransKernel r = 
    let rmap = toMap $ rmReflex $ rmSym r
        insDirR k set m = Map.insert k (dirRight set) m
        dirRight set = set Set.\\ transRight set
        transRight =  Set.unions . List.map lkup . Set.toList
        lkup = (\ e -> maybe Set.empty id (Map.lookup e rmap))
        filterEmptySet = Map.filter (not . Set.null)  
        addSym sm =                     
            Map.mapWithKey 
                      (\ k s -> Set.delete k $ 
                                Set.union s $ 
                                Map.findWithDefault Set.empty k sm)
    in Rel $ filterEmptySet $ 
             addSym (symmetricMap r) $ 
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
    Map.fold(\ e rs -> rs || (t1 `Set.member` e && 
                              t2 `Set.member` e)) False . toMap
