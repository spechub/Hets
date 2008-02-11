{- |
Module      :  $Header$
Description :  Tree-based implementation of 'Graph' and 'DynGraph' using Data.Map
Copyright   :  (c) Martin Erwig, Christian Maeder and Uni Bremen 1999-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Tree-based implementation of 'Graph' and 'DynGraph' using Data.IntMap
instead of Data.Graph.Inductive.Internal.FiniteMap
-}

module Common.Lib.Graph
  ( Gr
  , convertToMap
  , unsafeConstructGr
  , getPaths
  , getPathsTo
  , rmIsolated
  ) where

import Data.Graph.Inductive.Graph
import qualified Data.IntMap as Map
import Data.List (partition)

-- | the graph type constructor
newtype Gr a b = Gr { convertToMap :: Map.IntMap (Adj b, a, Adj b) }

unsafeConstructGr :: Map.IntMap (Adj b, a, Adj b) -> Gr a b
unsafeConstructGr = Gr

type GraphRep a b = Map.IntMap (Context' a b)
type Context' a b = (Adj b, a, Adj b)

instance (Show a,Show b) => Show (Gr a b) where
  show (Gr g) = showGraph g

instance Graph Gr where
  empty = Gr Map.empty
  isEmpty (Gr g) = Map.null g
  match = matchGr
  mkGraph vs es = (insEdges es . insNodes vs) empty
  labNodes = map (\ (v, (_, l, _)) -> (v, l)) . Map.toList . convertToMap
  -- more efficient versions of derived class members
  --
  matchAny g = case Map.keys $ convertToMap g of
    [] -> error "Match Exception, Empty Graph"
    h : _ -> let (Just c, g') = matchGr h g in (c, g')
  noNodes (Gr g) = Map.size g
  nodeRange (Gr g) = case Map.keys g of
    [] -> (0, -1)
    ks@(h : _) -> (h, last ks)
  labEdges =
    concatMap (\ (v, (_ ,_ , s)) -> map (\ (l, w) -> (v, w, l)) s)
    . Map.toList . convertToMap

instance DynGraph Gr where
  (p, v, l, s) & Gr g = let
    g1 = Map.insert v (p, l, s) g
    g2 = updAdj g1 p $ addSucc v
    g3 = updAdj g2 s $ addPred v
    in if Map.member v g then error $ "Node Exception, Node: " ++ show v
       else Gr g3

----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------

showGraph :: (Show a, Show b) => GraphRep a b -> String
showGraph gr = unlines $ map (\ (v, (_, l', s)) ->
                           show v ++ ":" ++ show l' ++ " ->" ++ show s)
                $ Map.toList gr

{- here cyclic edges are omitted as predecessors, thus they only count
as outgoing and not as ingoing! Therefore it is enough that only
successors are filtered during deletions. -}
matchGr :: Node -> Gr a b -> Decomp Gr a b
matchGr v (Gr g) = case Map.lookup v g of
  Nothing -> (Nothing, Gr g)
  Just (p, l, s) -> let
    s' = filter ((/= v) . snd) s
    p' = filter ((/= v) . snd) p
    g' = Map.delete v g
    g1 = updAdj g' s' $ clearPred v
    g2 = updAdj g1 p' $ clearSucc v
    in (Just (p', v, l, s), Gr g2)

addSucc :: Node -> b -> Context' a b -> Context' a b
addSucc v l (p, l', s) = (p, l', (l, v) : s)

addPred :: Node -> b -> Context' a b -> Context' a b
addPred v l (p, l', s) = ((l, v) : p, l', s)

clearSucc :: Node -> b -> Context' a b -> Context' a b
clearSucc v _ (p, l, s) = (p, l, filter ((/= v) . snd) s)

clearPred :: Node -> b -> Context' a b -> Context' a b
clearPred v _ (p, l, s) = (filter ((/= v) . snd) p, l, s)

updAdj :: GraphRep a b -> Adj b -> (b -> Context' a b -> Context' a b)
       -> GraphRep a b
updAdj g []         _              = g
updAdj g ((l,v):vs) f | Map.member v g = updAdj (Map.adjust (f l) v g) vs f
                      | otherwise  = error ("Edge Exception, Node: "++show v)

{- | compute the possible cycle free paths from a start node.
     The result paths are given in reverse order! -}
getPaths :: [LEdge b] -> Node -> Gr a b -> [[LEdge b]]
getPaths path src gr = case matchGr src gr of
    (Just (_, _, _, s), ng) -> let
      in concatMap (\ (lbl, tgt) -> let np = (src, tgt, lbl) : path in
             np : getPaths np tgt ng) $ filter ((/= src) . snd) s
    _ -> error "getPaths"

-- | compute the possible cycle free paths from a start node to a target node.
getPathsTo :: [LEdge b] -> Node -> Node -> Gr a b -> [[LEdge b]]
getPathsTo path src tgt gr = case matchGr tgt gr of
    (Just (p, _, _, _), ng) -> let
      (srcEdges, nxtEdges) = partition ((== src) . snd) p
      in map (\ (lbl, nxt) -> (nxt, tgt, lbl) : path) srcEdges
       ++ concatMap (\ (lbl, nxt) -> getPathsTo ((nxt, tgt, lbl) : path)
                     src nxt ng) nxtEdges
    _ -> error "getPathsTo"

-- | remove isolated nodes without edges
rmIsolated :: Gr a b -> Gr a b
rmIsolated (Gr m) = Gr $ Map.filter (\ (p, _, s) -> not (null p && null s)) m
