{- |
Module      :  $Header$
Description :  colimit of an arbitrary diagram in Set
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Computes the colimit of an arbitrary diagram in Set:
  - the set is the disjoint union of all sets in the diagram
    (which we obtain by pairing elements with the node number)
    factored by the equivalence generated by the pairs (x, f_i(x)),
    with i an arrow in the diagram
  - structural morphisms are factorizations

-}

module Common.SetColimit(
    computeColimitSet,
    addIntToSymbols
  )
 where

import Common.Id
import Common.Lib.Graph
import Common.Lib.Rel (leqClasses)

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

compose :: (Ord a) => Set.Set (a, Int) ->
                      Map.Map (a, Int) (a, Int) ->
                      Map.Map (a, Int) (a, Int) ->
                      Map.Map (a, Int) (a, Int)
compose s f g = Set.fold ( \ i h ->
                               let
                                i' = Map.findWithDefault i i f
                                j = Map.findWithDefault i' i' g in
                               if i == j then h else Map.insert i j h)
                Map.empty s

coeq :: (Ord a) =>
        Set.Set (a, Int) -> Set.Set (a, Int) ->
        Map.Map (a, Int) (a, Int) -> Map.Map (a, Int) (a, Int) ->
        (Set.Set (a, Int), Map.Map (a,Int) (a, Int))
coeq sSet tSet f1 f2 =
 case Set.elems sSet of
   [] -> (tSet, Map.empty)
   x:xs -> if null xs then let
             f1x = Map.findWithDefault x x f1
             f2x = Map.findWithDefault x x f2
            in if f1x == f2x then (tSet, Map.empty)
                else (Set.difference tSet $ Set.singleton f2x,
                      Map.fromList [(f2x, f1x)])
           else let
             a1 = Set.singleton x
             a2 = Set.difference sSet a1
             (c, cf) = coeq a1 tSet f1 f2
             cf1 = compose a2 f1 cf
             cf2 = compose a2 f2 cf
             (d, df) = coeq a2 c cf1 cf2
             coeqf = compose tSet cf df
            in (d, coeqf)

computeColimitSet :: (Ord a) =>
                     Gr (Set.Set a) (Int, Map.Map a a) ->
                     (Set.Set (a, Node), Map.Map Node (Map.Map a (a, Node)))
computeColimitSet graph = let
   unionSet = foldl Set.union Set.empty $
               map (\(n, s) -> Set.map (\x -> (x, n)) s) $ labNodes graph
   inclMap = Map.fromAscList $ map (\ (n, _) ->(n, Map.empty)) $ labNodes graph
   (colim, morMap) = computeCoeqs graph (unionSet, inclMap) $ labEdges graph
   morMap' = Map.map
               (\f -> Map.fromAscList $ map (\((x,_),z) -> (x,z))$
                      Map.toList f)
               morMap
  in (colim, morMap')

computeCoeqs :: (Ord a) =>
      Gr (Set.Set a) (Int, Map.Map a a) ->
      (Set.Set (a, Node), Map.Map Node (Map.Map (a, Node) (a, Node))) ->
      [LEdge (Int, Map.Map a a)] ->
      (Set.Set (a, Node), Map.Map Node (Map.Map (a, Node) (a, Node)))
computeCoeqs graph (colim, morMap) edgeList =
  case edgeList of
   [] -> (colim, morMap)
   (sn, tn, (_, f)):edges' -> let
     Just sset = lab graph sn
     f1 = morMap Map.! sn
     f' = Map.fromList $ map (\x -> ((x,sn),(Map.findWithDefault x x f, tn))) $
          Set.toList sset
     f2 = Map.map (\x -> Map.findWithDefault x  x (morMap Map.! tn)) f'
     (colim', coeqMor) = coeq (Set.map (\x -> (x, sn)) sset) colim f1 f2
     morMap' = Map.fromList $
               map (\(n, g) ->let
                     Just nset = lab graph n
                              in(n, Map.fromAscList $
                               map (\x -> let
                                      y = Map.findWithDefault x x g
                                     in (x,Map.findWithDefault y y coeqMor)) $
                               Set.toList $ Set.map (\x-> (x,n)) nset ))
               $ Map.toList  morMap
    in computeCoeqs graph (colim', morMap') edges'

class (Eq a, Ord a) => SymbolName a where
  addIntAsSuffix :: (a, Int) -> a

instance SymbolName Id where
 addIntAsSuffix (x,y) = appendNumber x y

addIntToSymbols :: (SymbolName a) =>
               (Set.Set (a, Node), Map.Map Node (Map.Map a (a, Node))) ->
               (Set.Set a, Map.Map Node (Map.Map a a))
addIntToSymbols (set, fun) = let
  fstEqual (x1,_) (x2,_) = x1 == x2
  partList pairSet = leqClasses fstEqual pairSet
  namePartitions elemList f0 s1 f1 = case elemList of
   [] -> (s1, f1)
   p:ps -> if length p == 1 then
     -- a single element with this name,it can be kept
    let s2 = Set.insert (fst $ head p) s1
        updateF node = Map.union (Map.findWithDefault (error "f1") node f1) $
                       Map.fromList $ map (\x -> (x, fst $ head p)) $
                       filter (\x -> Map.findWithDefault (error "fo(node)") x
                                      (Map.findWithDefault (error "f0") node f0)
                                     == head p) $
                       Map.keys $ Map.findWithDefault (error "f0")
                                   node f0
        f2 = Map.fromList $ zip (Map.keys f0) $ map updateF $ Map.keys f0
    in namePartitions ps f0 s2 f2
                else
     --several elements with same name, the number is added at the end
    let s2 = Set.union s1 $ Set.fromList $ map addIntAsSuffix p
        updateF node = Map.union (Map.findWithDefault (error "f1") node f1) $
             Map.fromList $
             map ( \x -> (x, addIntAsSuffix $
                                  Map.findWithDefault (error "addSuffixToId") x
                                  (Map.findWithDefault (error "f0") node f0))) $
             filter (\x -> (Map.findWithDefault (error "fo(node)") x
                           (Map.findWithDefault (error "f0") node f0))
                           `elem` p) $
             Map.keys $ Map.findWithDefault (error "f0") node f0
        f2 = Map.fromList $ zip (Map.keys f0) $ map updateF $ Map.keys f0
    in namePartitions ps f0 s2 f2
 in namePartitions (partList set) fun (Set.empty) $
    Map.fromList $ zip (Map.keys fun) (repeat Map.empty)


