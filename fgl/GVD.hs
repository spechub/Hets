--
--  GVD.hs -- Graph Voronoi Diagram (c) 2000 by Martin Erwig
--
module GVD (
   Voronoi,
   gvdIn,gvdOut,
   voronoiSet,nearestNode,nearestDist,nearestPath,
--    vd,nn,ns,
--    vdO,nnO,nsO
) where

import Maybe (listToMaybe)
import List (nub)

import qualified Heap as H

import Graph
-- import GraphData
import Basic (grev)
import SP (dijkstra)
import RootPath


type Voronoi a = LRTree a

gvdIn :: Real b => [Node] -> Graph a b -> Voronoi b
gvdIn vs g = gvdOut vs (grev g)

gvdOut :: Real b => [Node] -> Graph a b -> Voronoi b
gvdOut vs = dijkstra (H.build (map (:[]) (zip vs (repeat 0))))

voronoiSet :: Real b => Node -> Voronoi b -> [Node]
voronoiSet v = nub . concat . filter (\p->last p==v) . map (map fst)

maybePath :: Real b => Node -> Voronoi b -> Maybe (LPath b)
maybePath v = listToMaybe . filter (\((w,_):_)->w==v)

nearestNode :: Real b => Node -> Voronoi b -> Maybe Node
nearestNode v = fmap (last . map fst) . maybePath v

nearestDist :: Real b => Node -> Voronoi b -> Maybe b
nearestDist v = fmap (last . map snd) . maybePath v

nearestPath :: Real b => Node -> Voronoi b -> Maybe Path
nearestPath v = fmap (map fst) . maybePath v


-- vd = gvdIn [4,5] vor
-- vdO = gvdOut [4,5] vor
-- nn = map (flip nearestNode vd) [1..8]
-- nnO = map (flip nearestNode vdO) [1..8]
-- ns = map (flip voronoiSet vd) [1..8]
-- nsO = map (flip voronoiSet vdO) [1..8]
