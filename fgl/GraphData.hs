--
--  GraphData.hs -- Example Graphs 
--
--
module GraphData (
   a,b,c,e,ab,loop,cyc3,abb,dag3,dag4,
   d1,d3,g3,g3',
   clr479,clr486,clr489,clr508,clr528,kin248,vor,
   ucycle,star
) where

import Graph
import Basic

----------------------------------------------------------------------
-- EXAMPLE GRAPHS
----------------------------------------------------------------------


-- some auxiliary functions
--   genUNodes : generate list of unlabeled nodes
--   genNodes  : generate list of labeled nodes
--   labUEdges     : denote unlabeled edges
--   noEdges   : empty (unlabeled) edge list
-- genUNodes :: Int -> [UNode]
-- genUNodes n = zip [1..n] (repeat ())

genLNodes :: Enum a => a -> Int -> [LNode a]
genLNodes c i = take i (zip [1..] [c..])

-- labUEdges :: [Edge] -> [UEdge]
-- labUEdges = map (\(i,j) -> (i,j,()))

noEdges :: [UEdge]
noEdges = [] 


-- some small graphs
--
a    = embed ([],1,'a',[]::[((),Node)]) empty --  just a node
b    = mkGraph (zip [1..2] "ab") noEdges      --  just two nodes
c    = mkGraph (zip [1..3] "abc") noEdges     --  just three nodes
e    = embed ([((),1)],2,'b',[]) a            --  just one edge a-->b
loop = embed ([],1,'a',[((),1)]) empty        --  loop on single node
ab   = embed ([((),1)],2,'b',[((),1)]) a      --  cycle of two nodes:  a<-->b
cyc3 = buildGr                                --  cycle of three nodes
       [([("ca",3)],1,'a',[("ab",2)]),
                ([],2,'b',[("bc",3)]),
                ([],3,'c',[])]
abb  = mkGraph (zip [1..2] "ab") (labUEdges [(2,2)]) -- a and loop on b

dag3 = mkGraph (zip [1..3] "abc") (labUEdges [(1,3)])
dag4 = mkGraph (genLNodes 1 4) (labUEdges [(1,2),(1,4),(2,3),(2,4),(4,3)])

d1 = mkGraph (genLNodes 1 2) [(1,2,1)]
d3 = mkGraph (genLNodes 1 3) [(1,2,1),(1,3,4),(2,3,2)] 

g3 = ([("left",2),("up",3)],1,'a',[("right",2)]) &
                        ([],2,'b',[("down",3)]) &
                        ([],3,'c',[]) & empty

g3' = ([("down",2)], 3,'c',[("up",1)])   &
      ([("right",1)],2,'b',[("left",1)]) &
                 ([],1,'a',[])           & empty
      
-- some functions to create (regular) graphs
--
ucycle :: Int -> UGraph
ucycle n = mkUGraph vs (map (\v->(v,v `mod` n+1)) vs)
           where vs = [1..n]

star :: Int -> UGraph
star n = mkUGraph [1..n] (map (\v->(1,v)) [2..n])


-- more graphs (Book<page>)
--
-- clr : Cormen/Leiserson/Rivest
-- kin : Kingston
--
clr479 = mkGraph (genLNodes 'u' 6) 
         (labUEdges [(1,2),(1,4),(2,5),(3,5),(3,6),(4,2),(5,4),(6,6)])
clr486 :: Graph String ()
clr486 = mkGraph (zip [1..9] ["shorts","socks","watch","pants","shoes",
                              "shirt","belt","tie","jacket"])
                 (labUEdges [(1,4),(1,5),(2,5),(4,5),(4,7),(6,7),(6,8),(7,9),(8,9)])
clr489 = mkGraph (genLNodes 'a' 8)
                 (labUEdges [(1,2),(2,3),(2,5),(2,6),(3,4),(3,7),(4,3),(4,8),
                         (5,1),(5,6),(6,7),(7,6),(7,8),(8,8)])
clr508 = mkGraph (genLNodes 'a' 9)
                 [(1,2,4),(1,8,8),(2,3,8),(2,8,11),(3,4,7),(3,6,4),(3,9,2),
                  (4,5,9),(4,6,14),(5,6,10),(6,7,2),(7,8,1),(7,9,6),(8,9,7)]
clr528 = mkGraph [(1,'s'),(2,'u'),(3,'v'),(4,'x'),(5,'y')]
                 [(1,2,10),(1,4,5),(2,3,1),(2,4,2),(3,5,4),
                  (4,2,3),(4,3,9),(4,5,2),(5,1,7),(5,3,6)]
kin248 = mkGraph (genLNodes 1 10)
                 (labUEdges [(1,2),(1,4),(1,7),(2,4),(2,5),(3,4),(3,10),
                         (4,5),(4,8),(5,2),(5,3),(6,7),(7,6),(7,8),
                         (8,10),(9,9),(9,10),(10,8),(10,9)])
         -- this is the inverse graph shown on the bottom of the page

vor = mkGraph (zip [1..8] ["A","B","C","H1","H2","D","E","F"])
              [(1,4,3),(2,3,3),(2,4,3),(4,2,4),(4,6,2),
               (5,2,5),(5,3,6),(5,7,5),(5,8,6),
               (6,5,3),(6,7,2),(7,8,3),(8,7,3)]

