--
--  BFS.hs -- Breadth First Search  (c) 2000 by Martin Erwig
--
module BFS (
   bfs,bfsn,bfsWith,bfsnWith,           -- bfs node list
   level,leveln,                        -- node list + depth info
   bfe,bfen,                            -- bfs edges
   bft,                                 -- bfs tree
   esp,                                 -- shortest path (no. of edges)
) where

import Maybe (fromMaybe)
import Graph
import RootPath


-- bfs (node list ordered by distance)
--
-- TO DO: replace ++ with amortized O(1) queue (eg, Burton)
--
bfsnWith :: (Context a b -> c) -> [Node] -> Graph a b -> [c]
bfsnWith f vs     g | null vs || isEmpty g = []
bfsnWith f (v:vs) g = case match v g of
                       (Just c,g')  -> f c:bfsnWith f (vs++suc' c) g'
                       (Nothing,g') -> bfsnWith f vs g' 

bfsn :: [Node] -> Graph a b -> [Node]
bfsn = bfsnWith node'

bfsWith :: (Context a b -> c) -> Node -> Graph a b -> [c]
bfsWith f v = bfsnWith f [v]

bfs :: Node -> Graph a b -> [Node]
bfs = bfsWith node'

 

-- level (extension of bfs giving the depth of each node)
--
level :: Node -> Graph a b -> [(Node,Int)]
level v = leveln [(v,0)]

suci c i = zip (suc' c) (repeat i)

leveln :: [(Node,Int)] -> Graph a b -> [(Node,Int)]
leveln vs         g | null vs || isEmpty g = []
leveln ((v,j):vs) g = case match v g of
                        (Just c,g')  -> (v,j):leveln (vs++suci c (j+1)) g'
                        (Nothing,g') -> leveln vs g'  

-- bfe (breadth first edges)
-- remembers predecessor information
--
bfe :: Node -> Graph a b -> [Edge]
bfe v = bfen [(v,v)]

outU c = map (\(v,w,_)->(v,w)) (out' c)

bfen :: [Edge] -> Graph a b -> [Edge]
bfen vs         g | null vs || isEmpty g = []
bfen ((u,v):vs) g = case match v g of
                      (Just c,g')  -> (u,v):bfen (vs++outU c) g'
                      (Nothing,g') -> bfen vs g'  


-- bft (breadth first search tree)
-- here: with inward directed trees
--
-- bft :: Node -> Graph a b -> IT.InTree Node
-- bft v g = IT.build $ map swap $ bfe v g
--           where swap (x,y) = (y,x)
-- 
-- sp (shortest path wrt to number of edges)
--
-- sp :: Node -> Node -> Graph a b -> [Node]
-- sp s t g = reverse $ IT.rootPath (bft s g) t


-- faster shortest paths 
-- here: with root path trees
-- 
bft :: Node -> Graph a b -> RTree
bft v = bf [[v]]

bf :: [Path] -> Graph a b -> RTree
bf ps           g | null ps || isEmpty g = []
bf (p@(v:_):ps) g = case match v g of
                      (Just c,g')  -> p:bf (ps++map (:p) (suc' c)) g'
                      (Nothing,g') -> bf ps g'  

esp :: Node -> Node -> Graph a b -> Path
esp s t = getPath t . bft s

