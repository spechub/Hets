--
--  SP.hs -- Dijkstra's Shortest Path Algorithm  (c) 2000 by Martin Erwig
--
module SP (
   spTree,spLength,sp,                           -- shortest paths
   dijkstra
) where

import qualified Heap as H

import Graph
import RootPath


expand :: Real b => b -> LPath b -> Context a b -> [H.Heap (LPath b)]
expand d p (_,_,_,s) = map (\(l,v)->H.unit ((v,l+d):p)) s

dijkstra :: Real b => H.Heap (LPath b) -> Graph a b -> LRTree b
dijkstra h g | H.isEmpty h || isEmpty g = []
dijkstra h g =
    case match v g of
         (Just c,g')  -> p:dijkstra (H.mergeAll (h':expand d p c)) g'
         (Nothing,g') -> dijkstra h' g'  
    where (p@((v,d):_),h') = H.splitMin h
        
spTree :: Real b => Node -> Graph a b -> LRTree b
spTree v = dijkstra (H.unit [(v,0)])

spLength :: Real b => Node -> Node -> Graph a b -> b
spLength s t = getDistance t . spTree s

sp :: Real b => Node -> Node -> Graph a b -> Path
sp s t = map fst . getLPath t . spTree s
