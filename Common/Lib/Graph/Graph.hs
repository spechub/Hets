------------------------------------------------------------------------------
--  
--  Graph.hs -- Static and Dynamic Inductive Graphs  
--
--  (c) 1999-2002 by Martin Erwig [see file COPYRIGHT]
--
--  Contents:
--  * General type definitions
--  * Graph type classes to overload graph operations for different implementations
--  * Derived graph operations
--  
--  Graph Implementations are contained in the modules/files:
--  * TreeGraph.hs  (dynamic graphs)
--  * IOArrGraph.hs (static graphs)
--  
--  Example Graphs are contained in the module/file:
--  * GraphData.hs
--
------------------------------------------------------------------------------
module Graph 
(
-- types
   Node,LNode,UNode,                    -- plain, labeled, and unit-labeled node
   Edge,LEdge,UEdge,                    -- plain, labeled, and unit-labeled edge
   Adj,Context,MContext,Decomp,GDecomp, -- contexts for inductive graph view
   Path,LPath,UPath,                    -- plain, labeled, and unit-labeled path
-- classes
   Graph(..), 
   DynGraph(..),
-- operations
   ufold,gmap,nmap,emap,                -- graph folds and maps
   nodes,edges,labEdges,newNodes,gelem, -- graph projection
   insNode,insEdge,delNode,delEdge,     -- graph construction & destruction
   insNodes,insEdges,delNodes,delEdges,
   buildGr,mkUGraph,
   context,lab,neighbors,               -- graph inspection
   suc,pre,lsuc,lpre,
   out,inn,outdeg,indeg,deg,
   node',lab',labNode',neighbors',      -- context inspection
   suc',pre',lpre',lsuc',
   out',inn',outdeg',indeg',deg'
) 
where


import List (sortBy)


{- Signatures:

-- basic operations
empty      ::    Graph gr => gr a b
isEmpty    ::    Graph gr => gr a b -> Bool
match      ::    Graph gr => Node -> gr a b -> Decomp gr a b
mkGraph    ::    Graph gr => [LNode a] -> [LEdge b] -> gr a b
(&)        :: DynGraph gr => Context a b -> gr a b -> gr a b

-- graph folds and maps
ufold      :: Graph gr => ((Context a b) -> c -> c) -> c -> gr a b -> c
gmap       :: Graph gr => (Context a b -> Context c d) -> gr a b -> gr c d
nmap       :: Graph gr => (a -> c) -> gr a b -> gr c b
emap       :: Graph gr => (b -> c) -> gr a b -> gr a c

-- graph projection
matchAny   :: Graph gr => gr a b -> GDecomp g a b
nodes      :: Graph gr => gr a b -> [Node]
edges      :: Graph gr => gr a b -> [Edge]
labNodes   :: Graph gr => gr a b -> [LNode a]
labEdges   :: Graph gr => gr a b -> [LEdge b]
newNodes   :: Graph gr => Int -> gr a b -> [Node]
noNodes    :: Graph gr => gr a b -> Int
nodeRange  :: Graph gr => gr a b -> (Node,Node)
gelem      :: Graph gr => Node -> gr a b -> Bool

-- graph construction & destruction
insNode    :: DynGraph gr => LNode a   -> gr a b -> gr a b
insEdge    :: DynGraph gr => LEdge b   -> gr a b -> gr a b
delNode    ::    Graph gr => Node      -> gr a b -> gr a b
delEdge    :: DynGraph gr => Edge      -> gr a b -> gr a b
insNodes   :: DynGraph gr => [LNode a] -> gr a b -> gr a b
insEdges   :: DynGraph gr => [LEdge b] -> gr a b -> gr a b
delNodes   ::    Graph gr => [Node]    -> gr a b -> gr a b
delEdges   :: DynGraph gr => [Edge]    -> gr a b -> gr a b
buildGr    :: DynGraph gr => [Context a b] -> gr a b
mkUGraph   :: DynGraph gr => [Node] -> [Edge] -> gr () ()

-- graph inspection
context    :: Graph gr => gr a b -> Node -> Context a b
lab        :: Graph gr => gr a b -> Node -> Maybe a
neighbors  :: Graph gr => gr a b -> Node -> [Node] 
suc        :: Graph gr => gr a b -> Node -> [Node]
pre        :: Graph gr => gr a b -> Node -> [Node] 
lsuc       :: Graph gr => gr a b -> Node -> [(Node,b)]
lpre       :: Graph gr => gr a b -> Node -> [(Node,b)] 
out        :: Graph gr => gr a b -> Node -> [LEdge b] 
inn        :: Graph gr => gr a b -> Node -> [LEdge b] 
outdeg     :: Graph gr => gr a b -> Node -> Int
indeg      :: Graph gr => gr a b -> Node -> Int
deg        :: Graph gr => gr a b -> Node -> Int

-- context inspection
node'      :: Context a b -> Node
lab'       :: Context a b -> a
labNode'   :: Context a b -> LNode a
neighbors' :: Context a b -> [Node] 
suc'       :: Context a b -> [Node]
pre'       :: Context a b -> [Node] 
lpre'      :: Context a b -> [(Node,b)] 
lsuc'      :: Context a b -> [(Node,b)]
out'       :: Context a b -> [LEdge b] 
inn'       :: Context a b -> [LEdge b] 
outdeg'    :: Context a b -> Int
indeg'     :: Context a b -> Int
deg'       :: Context a b -> Int

-}


----------------------------------------------------------------------
-- BASIC TYPES 
----------------------------------------------------------------------

-- node and edge types
-- 
type  Node   = Int
type LNode a = (Node,a)
type UNode   = LNode ()

type  Edge   = (Node,Node)
type LEdge b = (Node,Node,b)
type UEdge   = LEdge ()

type Path    = [Node]
type LPath a = [LNode a]
type UPath   = [UNode]


-- types supporting inductive graph view
--
type Adj b        = [(b,Node)]
type Context a b  = (Adj b,Node,a,Adj b) -- Context a b "=" Context' a b "+" Node
type MContext a b = Maybe (Context a b)
type Decomp g a b = (MContext a b,g a b)
type GDecomp g a b  = (Context a b,g a b)

type UContext     = ([Node],Node,[Node])
type UDecomp g    = (Maybe UContext,g)



----------------------------------------------------------------------
-- GRAPH CLASSES 
----------------------------------------------------------------------

-- 
-- We define two graph classes:
--
--   Graph:    static, decomposable graphs
--             static means that a graph itself cannot be changed
--             
--   DynGraph: dynamic, extensible graphs
--             dynamic graphs inherit all operations from static graphs
--             but also offer operations to extend and change graphs
--
-- Each class contains in addition to its essential operations those
-- derived operations that might be overwritten by a more efficient
-- implementation in an instance definition.
-- 
-- Note that labNodes is essentially needed because the default definition
-- for matchAny is based on it: we need some node from the graph to define
-- matchAny in terms od match. Alternatively, we could have made matchAny 
-- essential and have labNodes defined in terms of ufold and matchAny. 
-- However, in general, labNodes seems to be (at least) as easy to define 
-- as matchAny. We have chosen labNodes instead of the function nodes since 
-- nodes can be easily derived from labNodes, but not vice versa.
--

class Graph gr where
  -- essential operations
  empty     :: gr a b
  isEmpty   :: gr a b -> Bool
  match     :: Node -> gr a b -> Decomp gr a b
  mkGraph   :: [LNode a] -> [LEdge b] -> gr a b
  labNodes  :: gr a b -> [LNode a]
  -- derived operations
  matchAny  :: gr a b -> GDecomp gr a b
  noNodes   :: gr a b -> Int
  nodeRange :: gr a b -> (Node,Node)
  labEdges  :: gr a b -> [LEdge b]
  -- default implementation of derived operations
  matchAny g = case labNodes g of
                 []      -> error "Match Exception, Empty Graph"
                 (v,_):_ -> (c,g') where (Just c,g') = match v g 
  noNodes = length . labNodes 
  nodeRange g = (minimum vs,maximum vs) where vs = map fst (labNodes g)
  labEdges = ufold (\(p,v,l,s)->((map (\(l,w)->(v,w,l)) s)++)) []


class Graph gr => DynGraph gr where
  (&) :: Context a b -> gr a b -> gr a b
  



----------------------------------------------------------------------
-- DERIVED GRAPH OPERATIONS
----------------------------------------------------------------------


-- graph folds and maps
-- 
ufold :: Graph gr => ((Context a b) -> c -> c) -> c -> gr a b -> c
ufold f u g | isEmpty g = u
            | otherwise = f c (ufold f u g') 
            where (c,g') = matchAny g

gmap :: DynGraph gr => (Context a b -> Context c d) -> gr a b -> gr c d
gmap f = ufold (\c->(f c&)) empty

nmap :: DynGraph gr => (a -> c) -> gr a b -> gr c b
nmap f = gmap (\(p,v,l,s)->(p,v,f l,s))

emap :: DynGraph gr => (b -> c) -> gr a b -> gr a c
emap f = gmap (\(p,v,l,s)->(map1 f p,v,l,map1 f s))
         where map1 f = map (\(l,v)->(f l,v))


-- (additional) graph projection
-- [noNodes, nodeRange, labNodes, labEdges are defined in class Graph]
-- 
nodes :: Graph gr => gr a b -> [Node]
nodes = map fst . labNodes

edges :: Graph gr => gr a b -> [Edge]
edges = map (\(v,w,_)->(v,w)) . labEdges

newNodes :: Graph gr => Int -> gr a b -> [Node]
newNodes i g = [n+1..n+i] where (_,n) = nodeRange g

gelem :: Graph gr => Node -> gr a b -> Bool
gelem v g = case match v g of {(Just _,_) -> True; _ -> False}


-- graph construction & destruction
-- 
insNode :: DynGraph gr => LNode a -> gr a b -> gr a b
insNode (v,l) = (([],v,l,[])&)

insEdge :: DynGraph gr => LEdge b -> gr a b -> gr a b
insEdge (v,w,l) g = (pre,v,lab,(l,w):suc) & g'
                    where (Just (pre,_,lab,suc),g') = match v g

delNode :: Graph gr => Node -> gr a b -> gr a b
delNode v = delNodes [v]

delEdge :: DynGraph gr => Edge -> gr a b -> gr a b
delEdge (v,w) g = case match v g of
                  (Nothing,_)        -> g
                  (Just (p,v,l,s),g) -> (p,v,l,filter ((/=w).snd) s) & g

insNodes   :: DynGraph gr => [LNode a] -> gr a b -> gr a b
insNodes vs g = foldr insNode g vs

insEdges :: DynGraph gr => [LEdge b] -> gr a b -> gr a b
insEdges es g = foldr insEdge g es

delNodes :: Graph gr => [Node] -> gr a b -> gr a b
delNodes []     g = g
delNodes (v:vs) g = delNodes vs (snd (match v g))  

delEdges :: DynGraph gr => [Edge]    -> gr a b -> gr a b
delEdges es g = foldr delEdge g es

buildGr :: DynGraph gr => [Context a b] -> gr a b
buildGr = foldr (&) empty

-- mkGraph :: DynGraph gr => [LNode a] -> [LEdge b] -> gr a b
-- mkGraph vs es = (insEdges es . insNodes vs) empty

mkUGraph :: Graph gr => [Node] -> [Edge] -> gr () ()
mkUGraph vs es = mkGraph (labUNodes vs) (labUEdges es) 

labUEdges = map (\(v,w)->(v,w,()))
labUNodes = map (\v->(v,()))
 

-- graph inspection (for a particular node)
-- 
context :: Graph gr => gr a b -> Node -> Context a b
context g v = case match v g of
                (Nothing,_) -> error ("Match Exception, Node: "++show v)
                (Just c,_)  -> c 

lab :: Graph gr => gr a b -> Node -> Maybe a
lab g v = fst (match v g) >>= return.lab' 

neighbors :: Graph gr => gr a b -> Node -> [Node] 
neighbors = (\(p,_,_,s) -> map snd (p++s)) .: context

suc :: Graph gr => gr a b -> Node -> [Node]
suc = map snd .: context4

pre :: Graph gr => gr a b -> Node -> [Node] 
pre = map snd .: context1

lsuc :: Graph gr => gr a b -> Node -> [(Node,b)]
lsuc = map flip2 .: context4

lpre :: Graph gr => gr a b -> Node -> [(Node,b)] 
lpre = map flip2 .: context1

out :: Graph gr => gr a b -> Node -> [LEdge b] 
out g v = map (\(l,w)->(v,w,l)) (context4 g v)

inn :: Graph gr => gr a b -> Node -> [LEdge b] 
inn g v = map (\(l,w)->(w,v,l)) (context1 g v)

outdeg :: Graph gr => gr a b -> Node -> Int
outdeg = length .: context4

indeg :: Graph gr => gr a b -> Node -> Int
indeg  = length .: context1

deg :: Graph gr => gr a b -> Node -> Int
deg = (\(p,_,_,s) -> length p+length s) .: context


-- context inspection
-- 
node' :: Context a b -> Node
node' (_,v,_,_) = v

lab' :: Context a b -> a
lab' (_,_,l,_) = l

labNode' :: Context a b -> LNode a
labNode' (_,v,l,_) = (v,l)

neighbors' :: Context a b -> [Node] 
neighbors' (p,_,_,s) = map snd p++map snd s

suc' :: Context a b -> [Node]
suc' (_,_,_,s) = map snd s

pre' :: Context a b -> [Node] 
pre' (p,_,_,_) = map snd p

lpre' :: Context a b -> [(Node,b)] 
lpre' (p,_,_,_) = map flip2 p

lsuc' :: Context a b -> [(Node,b)]
lsuc' (_,_,_,s) = map flip2 s

out' :: Context a b -> [LEdge b] 
out' (_,v,_,s) = map (\(l,w)->(v,w,l)) s

inn' :: Context a b -> [LEdge b] 
inn' (p,v,_,_) = map (\(l,w)->(w,v,l)) p

outdeg' :: Context a b -> Int
outdeg' (_,_,_,s) = length s

indeg' :: Context a b -> Int
indeg' (p,_,_,_) = length p

deg' :: Context a b -> Int
deg' (p,_,_,s) = length p+length s


-- graph equality
--
nodeComp :: Eq b => LNode b -> LNode b -> Ordering
nodeComp n@(v,a) n'@(w,b) | n == n'   = EQ
                          | v<w       = LT
                          | otherwise = GT

slabNodes :: (Eq a,Graph gr) => gr a b -> [LNode a]
slabNodes = sortBy nodeComp . labNodes

edgeComp :: Eq b => LEdge b -> LEdge b -> Ordering
edgeComp e@(v,w,a) e'@(x,y,b) | e == e'              = EQ
                              | v<x || (v==x && w<y) = LT
                              | otherwise            = GT

slabEdges :: (Eq b,Graph gr) => gr a b -> [LEdge b]
slabEdges = sortBy edgeComp . labEdges

instance (Eq a,Eq b,Graph gr) => Eq (gr a b) where
  g == g' = slabNodes g == slabNodes g' && slabEdges g == slabEdges g'



----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------


-- auxiliary functions used in the implementation of the 
-- derived class members
-- 
(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
-- f .: g = \x y->f (g x y)
-- f .: g = (f .) . g
-- (.:) f = ((f .) .)
-- (.:) = (.) (.) (.)
(.:) = (.) . (.)

fst4 (x,_,_,_) = x
snd4 (_,x,_,_) = x
thd4 (_,_,x,_) = x
fth4 (_,_,_,x) = x

fst3 (x,_,_) = x
snd3 (_,x,_) = x
thd3 (_,_,x) = x

flip2 (x,y) = (y,x)


-- projecting on context elements
--
-- context1 g v = fst4 (contextP g v)
context1 :: Graph gr => gr a b -> Node -> Adj b
context2 :: Graph gr => gr a b -> Node -> Node
context3 :: Graph gr => gr a b -> Node -> a
context4 :: Graph gr => gr a b -> Node -> Adj b

context1 = fst4 .: context
context2 = snd4 .: context
context3 = thd4 .: context
context4 = fth4 .: context

