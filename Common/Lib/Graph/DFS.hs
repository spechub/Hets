------------------------------------------------------------------------------
--
--  DFS.hs -- Depth-First Search  
--
--  (c) 2000 - 2002 by Martin Erwig [see file COPYRIGHT]
--
------------------------------------------------------------------------------

module DFS (
   Tree (..),                            -- rose tree 
   dfs,dfs',dff,dff',                    -- depth first search
   dfsWith,
   udfs,udfs',udff,udff',                -- undirected depth first search
   rdff,rdff',                           -- reverse dfs
   topsort,scc,reachable,                -- applications of dfs/dff
   components,noComponents,isConnected   -- applications of udfs/udff   
) where


import Graph
import RoseTree


----------------------------------------------------------------------
-- DFS AND FRIENDS
----------------------------------------------------------------------

{-

  Classification of all 32 dfs functions:

    dfs-function ::= [direction]"df"structure["With"]["'"]
    direction  -->  "x" | "u" | "r"
    structure  -->  "s" | "f"

              |   structure
   direction  |   "s"   "f"
   ------------------------   + optional With + optional '
      "x"     | xdfs  xdff   
      " "     |  dfs   dff
      "u"     | udfs  udff
      "r"     | rdfs  rdff
   ------------------------

  Direction Parameter
  -------------------
   x : parameterized by a function that specifies which nodes 
       to be visited next

  " ": the "normal case: just follow successors
 
   u : undirected, ie, follow predecesors and successors
   
   r : reverse, ie, follow predecesors


  Structure Parameter
  -------------------
   s : result is a list of 
        (a) objects computed from visited contexts  ("With"-version)
        (b) nodes                                   (normal version)

   f : result is a tree/forest of 
        (a) objects computed from visited contexts  ("With"-version)
        (b) nodes                                   (normal version)

  Optional Suffixes
  -----------------
   With : objects to be put into list/tree are given by a function
          on contexts, default for non-"With" versions: nodes

   '    : parameter node list is given implicitly by the nodes of the 
          graph to be traversed, default for non-"'" versions: nodes
          must be provided explicitly


  Defined are only the following 18 most important function versions:

    xdfsWith
     dfsWith,dfsWith',dfs,dfs'
     udfs,udfs'
     rdfs,rdfs'
    xdffWith
     dffWith,dffWith',dff,dff'
     udff,udff'
     rdff,rdff'
    
  Others can be added quite easily if needed.
  
-}

-- fixNodes fixes the nodes of the graph as a parameter
--
fixNodes :: Graph gr => ([Node] -> gr a b -> c) -> gr a b -> c
fixNodes f g = f (nodes g) g


-- generalized depth-first search
--  (could also be simply defined as applying preorderF to the 
--   result of xdffWith)
--   
type CFun a b c = Context a b -> c

xdfsWith :: Graph gr => CFun a b [Node] -> CFun a b c -> [Node] -> gr a b -> [c]
xdfsWith _ _ vs     g | null vs || isEmpty g = []
xdfsWith d f (v:vs) g = case match v g of
                         (Just c,g')  -> f c:xdfsWith d f (d c++vs) g'
                         (Nothing,g') -> xdfsWith d f vs g'  


-- dfs
--
dfsWith :: Graph gr => CFun a b c -> [Node] -> gr a b -> [c]
dfsWith = xdfsWith suc'

dfsWith' :: Graph gr => CFun a b c -> gr a b -> [c]
dfsWith' f = fixNodes (dfsWith f)

dfs :: Graph gr => [Node] -> gr a b -> [Node]
dfs = dfsWith node'

dfs' :: Graph gr => gr a b -> [Node]
dfs' = dfsWith' node'


-- undirected dfs, ie, ignore edge directions
--
udfs :: Graph gr => [Node] -> gr a b -> [Node]
udfs = xdfsWith neighbors' node'  

udfs' :: Graph gr => gr a b -> [Node]
udfs' = fixNodes udfs


-- reverse dfs, ie, follow predecessors
--
rdfs :: Graph gr => [Node] -> gr a b -> [Node]
rdfs = xdfsWith pre' node'  

rdfs' :: Graph gr => gr a b -> [Node]
rdfs' = fixNodes rdfs


-- generalized depth-first forest
-- 
xdfWith :: Graph gr => CFun a b [Node] -> CFun a b c -> [Node] -> gr a b -> ([Tree c],gr a b)
xdfWith _ _ vs     g | null vs || isEmpty g = ([],g)
xdfWith d f (v:vs) g = case match v g of
                        (Nothing,g1) -> xdfWith d f vs g1 
                        (Just c,g1)  -> (Br (f c) ts:ts',g3) 
                                 where (ts,g2)  = xdfWith d f (d c) g1
                                       (ts',g3) = xdfWith d f vs g2 

xdffWith :: Graph gr => CFun a b [Node] -> CFun a b c -> [Node] -> gr a b -> [Tree c]
xdffWith d f vs g = fst (xdfWith d f vs g)


-- dff
--
dffWith :: Graph gr => CFun a b c -> [Node] -> gr a b -> [Tree c]
dffWith = xdffWith suc'

dffWith' :: Graph gr => CFun a b c -> gr a b -> [Tree c]
dffWith' f = fixNodes (dffWith f)

dff :: Graph gr => [Node] -> gr a b -> [Tree Node]
dff = dffWith node'

dff' :: Graph gr => gr a b -> [Tree Node]
dff' = dffWith' node'


-- undirected dff
--
udff :: Graph gr => [Node] -> gr a b -> [Tree Node]
udff = xdffWith neighbors' node'

udff' :: Graph gr => gr a b -> [Tree Node]
udff' = fixNodes udff


-- reverse dff, ie, following predecessors
--
rdff :: Graph gr => [Node] -> gr a b -> [Tree Node]
rdff = xdffWith pre' node'

rdff' :: Graph gr => gr a b -> [Tree Node]
rdff' = fixNodes rdff


----------------------------------------------------------------------
-- ALGORITHMS BASED ON DFS
----------------------------------------------------------------------

components :: Graph gr => gr a b -> [[Node]]
components = (map preorder) . udff'

noComponents :: Graph gr => gr a b -> Int
noComponents = length . components

isConnected :: Graph gr => gr a b -> Bool
isConnected = (==1) . noComponents

topsort :: Graph gr => gr a b -> [Node]
topsort = reverse . postorderF . dff'

scc :: Graph gr => gr a b -> [[Node]]
scc g = map preorder (rdff (topsort g) g)            -- optimized, using rdff
-- sccOrig g = map preorder (dff (topsort g) (grev g))  -- original by Sharir

reachable :: Graph gr => Node -> gr a b -> [Node]
reachable v g = preorderF (dff [v] g)

