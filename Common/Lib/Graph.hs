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
  , GrContext(..)
  , convertToMap
  , unsafeConstructGr
  , getPaths
  , getPathsTo
  , Common.Lib.Graph.delLEdge
  , insLEdge
  , rmIsolated
  ) where

import Data.Graph.Inductive.Graph as Graph
import qualified Data.IntMap as Map
import Data.List

-- | the graph type constructor
newtype Gr a b = Gr { convertToMap :: Map.IntMap (GrContext a b) }

data GrContext a b = GrContext
    { nodeLabel :: a
    , nodeSuccs :: Map.IntMap [b]
    , loops :: [b]
    , nodePreds :: Map.IntMap [b] }

unsafeConstructGr :: Map.IntMap (GrContext a b) -> Gr a b
unsafeConstructGr = Gr

instance (Show a,Show b) => Show (Gr a b) where
  show (Gr g) = showGraph g

instance Graph Gr where
  empty = Gr Map.empty
  isEmpty (Gr g) = Map.null g
  match = matchGr
  mkGraph vs es = (insEdges es . insNodes vs) empty
  labNodes = map (\ (v, c) -> (v, nodeLabel c)) . Map.toList . convertToMap
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
    concatMap (\ (v, cw) -> map (\ (l, w) -> (v, w, l))
              $ mkLoops v (loops cw) ++ mkAdj (nodeSuccs cw))
    . Map.toList . convertToMap

instance DynGraph Gr where
  (p, v, l, s) & gr = let
    mkMap = foldr (\ (e, w) -> Map.insertWith (++) w [e]) Map.empty
    pm = mkMap p
    sm = mkMap s
    in composeGr v GrContext
      { nodeLabel = l
      , nodeSuccs = Map.delete v sm
      , loops = Map.findWithDefault [] v pm ++ Map.findWithDefault [] v sm
      , nodePreds = Map.delete v pm } gr

showGraph :: (Show a, Show b) => Map.IntMap (GrContext a b) -> String
showGraph gr = unlines $ map
  (\ (v, c) ->
   shows v ": " ++ show (nodeLabel c)
   ++ showLinks
   ((case loops c of
       [] -> []
       l -> [(v, l)]) ++ Map.toList (nodeSuccs c)))
  $ Map.toList gr

showLinks :: Show b => [(Node, [b])] -> String
showLinks = concatMap $ \ (v, l) -> " - " ++
            concat (intersperse ", " $ map show l) ++ " -> " ++ shows v ";"

mkLoops :: Node -> [b] -> Adj b
mkLoops v = map (\ e -> (e, v))

mkAdj :: Map.IntMap [b] -> Adj b
mkAdj = concatMap (\ (w, l) -> map (\ e -> (e, w)) l) . Map.toList

{- here cyclic edges are omitted as predecessors, thus they only count
as outgoing and not as ingoing! Therefore it is enough that only
successors are filtered during deletions. -}
matchGr :: Node -> Gr a b -> Decomp Gr a b
matchGr v gr = case decomposeGr v gr of
  Nothing -> (Nothing, gr)
  Just (c, rg) -> (Just ( mkAdj $ nodePreds c , v , nodeLabel c
                        , mkLoops v (loops c) ++ mkAdj (nodeSuccs c)), rg)

decomposeGr :: Node -> Gr a b -> Maybe (GrContext a b, Gr a b)
decomposeGr v (Gr g) = case Map.lookup v g of
  Nothing -> Nothing
  Just c -> let
    g1 = Map.delete v g
    g2 = updAdj g1 (nodeSuccs c) $ clearPred v
    g3 = updAdj g2 (nodePreds c) $ clearSucc v
    in Just (c, Gr g3)

addSuccs :: Node -> [b] -> GrContext a b -> GrContext a b
addSuccs v ls c = c { nodeSuccs = Map.insert v ls $ nodeSuccs c }

addPreds :: Node -> [b] -> GrContext a b -> GrContext a b
addPreds v ls c = c { nodePreds = Map.insert v ls $ nodePreds c }

clearSucc :: Node -> [b] -> GrContext a b -> GrContext a b
clearSucc v _ c = c { nodeSuccs = Map.delete v $ nodeSuccs c }

clearPred :: Node -> [b] -> GrContext a b -> GrContext a b
clearPred v _ c = c { nodePreds = Map.delete v $ nodePreds c }

updAdj :: Map.IntMap (GrContext a b) -> Map.IntMap [b]
       -> ([b] -> GrContext a b -> GrContext a b) -> Map.IntMap (GrContext a b)
updAdj g m f = Map.foldWithKey (\ v ls r -> case Map.lookup v r of
    Nothing -> error $ "missing edge node: " ++ show v
    Just c -> Map.insert v (f ls c) r) g m

composeGr :: Node -> GrContext a b -> Gr a b -> Gr a b
composeGr v c (Gr g) = let
    g1 = updAdj g (nodePreds c) $ addSuccs v
    g2 = updAdj g1 (nodeSuccs c) $ addPreds v
    g3 = Map.insert v c g2
    in if Map.member v g then error $ "Node Exception, Node: " ++ show v
       else Gr g3

{- | compute the possible cycle free paths from a start node -}
getPaths :: Node -> Gr a b -> [[LEdge b]]
getPaths src gr = case decomposeGr src gr of
    Just (c, ng) ->
      Map.foldWithKey (\ nxt lbls l ->
           l ++ map (\ b -> [(src, nxt, b)]) lbls
             ++ concatMap (\ p -> map (\ b -> (src, nxt, b) : p) lbls)
                           (getPaths nxt ng)) [] $ nodeSuccs c
    _ -> error "getPaths"

-- | compute the possible cycle free paths from a start node to a target node.
getPathsTo :: Node -> Node -> Gr a b -> [[LEdge b]]
getPathsTo src tgt gr = case decomposeGr src gr of
    Just (c, ng) -> let
      s = nodeSuccs c
      in Map.foldWithKey (\ nxt lbls ->
            (++ concatMap (\ p -> map (\ b -> (src, nxt, b) : p) lbls)
                (getPathsTo nxt tgt ng)))
          (map (\ lbl -> [(src, tgt, lbl)]) $ Map.findWithDefault [] tgt s)
              (Map.delete tgt s)
    _ -> error "getPathsTo"

-- | delete a labeled edge from a graph
delLEdge :: (b -> b -> Ordering) -> LEdge b -> Gr a b -> Gr a b
delLEdge cmp (v, w, l) gr = let e = show (v, w) in case decomposeGr v gr of
    Just(c, ng) -> let
      sm = nodeSuccs c
      sl = Map.findWithDefault [] w sm
      ls = loops c
      b = v == w
      in case partition (\ k -> cmp k l == EQ) $ if b then ls else sl of
           ([], _) ->
               error $ "delLEdge no matching edge between: " ++ e
           ([_], rs) -> composeGr v (if b then c { loops = rs }
                           else c { nodeSuccs = if null rs
                                    then Map.delete w sm
                                    else Map.insert w rs sm }) ng
           _ -> error $ "delLEdge multiple matching edges between: "
                ++ show (v, w)
    _ -> error $ "delLEdge missing node " ++ show v ++ " for edge: " ++ e

-- | insert a labeled edge into a graph
insLEdge :: Bool -> (b -> b -> Ordering) -> LEdge b -> Gr a b -> Gr a b
insLEdge failIfExist cmp (v, w, l) gr =
  let e = show (v, w) in case decomposeGr v gr of
    Just (c, ng) -> let
      sm = nodeSuccs c
      sl = Map.findWithDefault [] w sm
      ls = loops c
      b = v == w
      in if any (\ k -> cmp k l == EQ) $ if b then ls else sl then
             if failIfExist then
                error $ "insLEdge multiple edge between: " ++ e
             else gr
         else composeGr v (if b then c { loops = insertBy cmp l ls }
                           else c { nodeSuccs = Map.insert w
                                    (insertBy cmp l sl) sm }) ng
    _ -> error $ "insLEdge missing node " ++ show v ++ " for edge: " ++ e

-- | remove isolated nodes without edges
rmIsolated :: Gr a b -> Gr a b
rmIsolated (Gr m) = Gr $ Map.filter
 (\ c -> not $ Map.null (nodeSuccs c) && Map.null (nodePreds c)) m
