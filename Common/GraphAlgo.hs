{- |
Module      :  ./Common/GraphAlgo.hs
Description :  Algorithms on Graphs
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  portable

-}

module Common.GraphAlgo where

import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

data Graph node edge = Graph {
 neighbours :: node -> [(edge, node)],
 weight :: edge -> Int
}

data Node = Node String deriving (Eq, Ord)
data Edge = Edge (String, String) deriving (Eq, Ord)

instance Show Node where
 show (Node s) = s

instance Show Edge where
 show (Edge (s1, s2)) = s1 ++ "," ++ s2

exampleGraph :: [(String, String)] -> Graph Node Edge
exampleGraph conns = Graph {
 neighbours = \ n -> map (\ (s1, s2) -> (Edge (s1, s2), Node s2)) $
  filter (\ (s, _) -> (Node s == n)) conns,
 weight = const 1
}

mapMin :: (a -> a -> Bool) -> Map.Map k a -> Maybe (k, a)
mapMin less = Map.foldrWithKey (\ k a b -> case b of
 Just (_, a1) -> if less a1 a then b else Just (k, a)
 Nothing -> Just (k, a)) Nothing

dijkstra :: (Show node, Show edge, Ord node) => node -> (node -> Bool)
             -> Graph node edge -> Maybe ([(node, edge)], node)
dijkstra start isEnd (Graph neighbours_ weight_) =
 let visited = snd $ adjust (Map.fromList [(start, (Nothing, 0))], Map.empty)
 in case mapMin (\ (_, w1) (_, w2) -> w1 < w2) $
          Map.filterWithKey (\ n _ -> isEnd n) visited of
     Just (end, _) -> maybe Nothing (\ p -> Just (reverse p, end))
               $ extractPath end visited
     _ -> Nothing
 where
  adjust (known, visited) =
   case mapMin (\ (_, w1) (_, w2) -> w1 < w2) known of
    Just (n, d@(_, n_weight)) ->
     let (known_, visited_) = (Map.delete n known,
                              Map.insert n d visited)
     in if isEnd n then (known_, visited_)
        else adjust $
         foldl (\ (known', visited') (e, next_n) ->
          case Map.lookup next_n visited' of
           Just (_, w) -> (known', if n_weight + weight_ e < w then
                           Map.insert next_n (Just (n, e), n_weight + weight_ e)
                            visited' else visited')
           Nothing -> (case Map.lookup next_n known' of
                       Just (_, w) -> if n_weight + weight_ e < w then
                        Map.insert next_n (Just (n, e), n_weight + weight_ e) known'
                        else known'
                       Nothing -> Map.insert next_n
                        (Just (n, e), n_weight + weight_ e) known', visited'))
         (known_, visited_) (neighbours_ n)
    Nothing -> (known, visited)
  extractPath n visited = case Map.lookup n visited of
   Just (Just (prev, e), _) -> case extractPath prev (Map.delete n visited) of
                          Just l -> Just $ (prev, e) : l
                          Nothing -> Nothing
   Just (Nothing, _) -> Just []
   Nothing -> Nothing

yen :: (Ord node, Eq edge, Show node, Show edge) => Int -> node -> (node -> Bool)
                                -> Graph node edge -> [([(node, edge)], node)]
yen k' start end g = case dijkstra start end g of
  Just (shortest_path, end') -> map (\ p -> (p, end')) $ yen_ (k' - 1) [shortest_path]
  Nothing -> []
 where
  yen_ k a = if k <= 0 then a
   else let b = mapMaybe (yen' k a) [0 .. (length (a !! (k' - k - 1)) - 1)]
        in case minPath b of
            Just m -> yen_ (k - 1) $ a ++ [m]
            Nothing -> a
  yen' k a i =
     let spurNode = fst $ (a !! (k' - k - 1)) !! i
         rootPath = take i (a !! (k' - k - 1))
         hide =
          concatMap (\ p -> [p !! i | take i p == rootPath]) a
         g' = g { neighbours = \ n -> filter (\ (e, _) -> notElem (n, e) hide) $
                   neighbours g n }
     in case dijkstra spurNode end g' of
         Just (spurPath, _) -> Just $ rootPath ++ spurPath
         Nothing -> Nothing
  minPath (p : ps) = case minPath ps of
   Just m -> Just $ if pathLen p < pathLen m then p else m
   Nothing -> Just p
  minPath [] = Nothing
  pathLen p = sum $ map (\ (_, e) -> (weight g e)) p

prettyPath :: (Show node, Show edge) => ([(node, edge)], node) -> String
prettyPath (p, last_node) =
  let (nodes, edges) = unzip p
      (nodes_s, edges_s) = (map show nodes,
       map (\ e -> " =(" ++ show e ++ ")=> ") edges)
  in foldl (\ s (n, e) -> s ++ n ++ e) "" (zip nodes_s edges_s) ++ show last_node

test_graph :: Graph Node Edge
test_graph = exampleGraph [("A", "B"), ("B", "C"), ("B", "E"), ("B", "D"), ("D", "E")]

test :: String
test = maybe "" prettyPath $
 dijkstra (Node "A") ((==) $ Node "E") test_graph

test1 :: [[String]]
test1 = map (map prettyPath)
 [yen i (Node "A") ((==) $ Node "E") test_graph | i <- [1 .. 3]]
