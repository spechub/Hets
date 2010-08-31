{- |
Module      :  $Header$
Description :  Tree-based implementation of 'Graph' and 'DynGraph'
  using Data.Map
Copyright   :  (c) Martin Erwig, Christian Maeder and Uni Bremen 1999-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Tree-based implementation of 'Graph' and 'DynGraph' using Data.IntMap
instead of Data.Graph.Inductive.Internal.FiniteMap
-}

module Common.Lib.Graph
  ( Gr(..)
  , GrContext(..)
  , unsafeConstructGr
  , decomposeGr
  , getPaths
  , getAllPathsTo
  , getPathsTo
  , getLEdges
  , Common.Lib.Graph.delLEdge
  , insLEdge
  , delLNode
  , labelNode
  , getNewNode
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

instance (Show a, Show b) => Show (Gr a b) where
  show (Gr g) = showGraph g

instance Graph Gr where
  empty = Gr Map.empty
  isEmpty (Gr g) = Map.null g
  match = matchGr
  mkGraph vs es = (insEdges es . insNodes vs) empty
  labNodes = map (\ (v, c) -> (v, nodeLabel c)) . Map.toList . convertToMap
  -- more efficient versions of derived class members
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
showGraph = unlines . map
  (\ (v, c) ->
   shows v ": " ++ show (nodeLabel c)
   ++ showLinks
   ((case loops c of
       [] -> []
       l -> [(v, l)]) ++ Map.toList (nodeSuccs c)))
  . Map.toList

showLinks :: Show b => [(Node, [b])] -> String
showLinks = concatMap $ \ (v, l) -> " - " ++
            intercalate ", " (map show l) ++ " -> " ++ shows v ";"

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
       -> ([b] -> GrContext a b -> GrContext a b)
       -> Map.IntMap (GrContext a b)
updAdj g m f = Map.foldWithKey (\ v -> updGrContext v . f) g m

updGrContext :: Node -> (GrContext a b -> GrContext a b)
             -> Map.IntMap (GrContext a b) -> Map.IntMap (GrContext a b)
updGrContext v f r = case Map.lookup v r of
    Nothing -> error $ "Common.Lib.Graph.updGrContext no node: " ++ show v
    Just c -> Map.insert v (f c) r

composeGr :: Node -> GrContext a b -> Gr a b -> Gr a b
composeGr v c (Gr g) = let
    g1 = updAdj g (nodePreds c) $ addSuccs v
    g2 = updAdj g1 (nodeSuccs c) $ addPreds v
    g3 = Map.insert v c g2
    in if Map.member v g
       then error $ "Common.Lib.Graph.composeGr no node: " ++ show v
       else Gr g3

-- | compute the possible cycle free paths from a start node
getPaths :: Node -> Gr a b -> [[LEdge b]]
getPaths src gr = case decomposeGr src gr of
    Just (c, ng) ->
      Map.foldWithKey (\ nxt lbls l ->
           l ++ map (\ b -> [(src, nxt, b)]) lbls
             ++ concatMap (\ p -> map (\ b -> (src, nxt, b) : p) lbls)
                           (getPaths nxt ng)) [] $ nodeSuccs c
    Nothing -> error $ "Common.Lib.Graph.getPaths no node: " ++ show src

-- | compute the possible cycle free reversed paths from a start node
getAllPathsTo :: Node -> Gr a b -> [[LEdge b]]
getAllPathsTo tgt gr = case decomposeGr tgt gr of
    Just (c, ng) ->
      Map.foldWithKey (\ nxt lbls l ->
           l ++ map (\ b -> [(nxt, tgt, b)]) lbls
             ++ concatMap (\ p -> map (\ b -> (nxt, tgt, b) : p) lbls)
                           (getAllPathsTo nxt ng)) [] $ nodePreds c
    Nothing -> error $ "Common.Lib.Graph.getAllPathsTo no node: " ++ show tgt

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
    Nothing -> error $ "Common.Lib.Graph.getPathsTo no node: " ++ show src

-- | get all the edge labels between two nodes
getLEdges :: Node -> Node -> Gr a b -> [b]
getLEdges v w (Gr m) = let err = "Common.Lib.Graph.getLEdges: no node " in
  case Map.lookup v m of
    Just c -> if v == w then loops c else
      Map.findWithDefault
        (if Map.member w m then [] else error $ err ++ show w)
        w $ nodeSuccs c
    Nothing -> error $ err ++ show v

showEdge :: Node -> Node -> String
showEdge v w = show v ++ " -> " ++ show w

-- | delete a labeled edge from a graph
delLEdge :: (b -> b -> Ordering) -> LEdge b -> Gr a b -> Gr a b
delLEdge cmp (v, w, l) (Gr m) =
  let e = showEdge v w
      err = "Common.Lib.Graph.delLEdge "
  in case Map.lookup v m of
    Just c -> let
      sm = nodeSuccs c
      b = v == w
      ls = if b then loops c else Map.findWithDefault [] w sm
      in case partition (\ k -> cmp k l == EQ) ls of
           ([], _) -> error $ err ++ "no edge: " ++ e
           ([_], rs) -> if b then Gr $ Map.insert v c { loops = rs } m else
             Gr $ updGrContext w
              ((if null rs then clearPred else addPreds) v rs)
              $ Map.insert v c
                { nodeSuccs = if null rs then Map.delete w sm else
                    Map.insert w rs sm } m
           _ -> error $ err ++ "multiple edges: " ++ e
    Nothing -> error $ err ++ "no node: " ++ show v ++ " for edge: " ++ e

-- | insert a labeled edge into a graph, returns False if edge exists
insLEdge :: Bool -> (b -> b -> Ordering) -> LEdge b -> Gr a b
         -> (Gr a b, Bool)
insLEdge failIfExist cmp (v, w, l) gr@(Gr m) =
  let e = showEdge v w
      err = "Common.Lib.Graph.insLEdge "
  in case Map.lookup v m of
    Just c -> let
      sm = nodeSuccs c
      b = v == w
      ls = if b then loops c else Map.findWithDefault [] w sm
      ns = insertBy cmp l ls
      in if any (\ k -> cmp k l == EQ) ls then
           if failIfExist then error $ err ++ "multiple edges: " ++ e
           else (gr, False)
         else (if b then Gr $ Map.insert v c { loops = ns } m else
                  Gr $ updGrContext w (addPreds v ns)
                  $ Map.insert v c { nodeSuccs = Map.insert w ns sm } m, True)
    Nothing -> error $ err ++ "no node: " ++ show v ++ " for edge: " ++ e

isIsolated :: GrContext a b -> Bool
isIsolated c = Map.null (nodeSuccs c) && Map.null (nodePreds c)

-- | delete a labeled node
delLNode :: (a -> a -> Bool) -> LNode a -> Gr a b -> Gr a b
delLNode eq (v, l) (Gr m) =
  let err = "Common.Lib.Graph.delLNode: node " ++ show v in
  case Map.lookup v m of
    Just c -> if isIsolated c && null (loops c) then
                  if eq l $ nodeLabel c then Gr (Map.delete v m)
                     else error $ err ++ " has a different label"
              else error $ err ++ " has remaining edges"
    Nothing -> error $ err ++ " is missing"

-- | sets the node with new label and returns the new graph and the old label
labelNode :: LNode a -> Gr a b -> (Gr a b, a)
labelNode (v, l) (Gr m) = case Map.lookup v m of
    Just c -> (Gr $ Map.insert v (c { nodeLabel = l }) m, nodeLabel c)
    Nothing -> error $ "Common.Lib.Graph.labelNode no node: " ++ show v

-- | returns one new node id for the given graph
getNewNode :: Gr a b -> Node
getNewNode g = case newNodes 1 g of
    [n] -> n
    _ -> error "Common.Lib.Graph.getNewNode"

-- | remove isolated nodes without edges
rmIsolated :: Gr a b -> Gr a b
rmIsolated (Gr m) = Gr $ Map.filter (not . isIsolated) m
