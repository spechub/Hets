--
--  Graph.hs -- Inductive Graphs  (c) 2000 by Martin Erwig
--
--  The implementation is based on extensible finite maps.
--  For fixed size graphs, see StaticGraph.hs
--
--  Example Graphs:      GraphData.hs
--
module Graph (
-- types
   Node,LNode,UNode,                  -- plain, labeled, and unit-labeled node
   Edge,LEdge,UEdge,                  -- plain, labeled, and unit-labeled edge
   Graph,UGraph,                      -- plain and unit-labeled graph
   Adj,Context,MContext(..),Decomp,GDecomp,     -- inductive graph view
   Path,LPath,UPath,                  -- plain, labeled, and unit-labeled path
-- main functions
   empty,embed,(&),match,matchP,matchAny,
   emptyU,embedU,matchU,matchAnyU,
-- derived operations
   isEmpty,matchSome,matchThe,context,contextP,
   delNode,delNodes,delEdge,delEdges,
   suc,pre,neighbors,out,inn,indeg,outdeg,deg,
   suc',pre',neighbors',out',inn',indeg',outdeg',deg',node',lab',
   noNodes,nodeRange,nodes,labNodes,edges,labEdges,
   -- graph folds
   --    ufold,gfold,  --> see Basic.hs
   -- graph transformations
   --    undir, gmap,  --> see Basic.hs
-- utilities to for (un)labeling
   labUEdges,labUNodes,labUAdj,
   unlabEdges,unlabNodes,unlabAdj,
-- utilities to build graphs
   newNodes,insNode,insNodes,insEdge,insEdges,
   mkGraph,mkUGraph,buildGr
) where

import SimpleMap
import Maybe (fromJust)


----------------------------------------------------------------------
-- TYPES
----------------------------------------------------------------------

-- basic types
-- 
type  Node     = Int
type LNode a   = (Node,a)
type UNode     = LNode ()

type  Edge     = (Node,Node)
type LEdge b   = (Node,Node,b)
type UEdge     = LEdge ()

data Graph a b = Graph (GraphRep a b)
type UGraph    = Graph () ()
-- type NGraph a  = Graph a () 
-- type EGraph b  = Graph () b 

type Path      = [Node]
type LPath a   = [LNode a]
type UPath     = [UNode]


-- types supporting inductive graph view
--
type Adj b        = [(b,Node)]
type Context a b  = (Adj b,Node,a,Adj b) -- Context a b "=" Context' a b "+" Node
type MContext a b = Maybe (Context a b)
type Decomp a b   = (MContext a b,Graph a b)
type GDecomp a b  = (Context a b,Graph a b)

type UContext     = ([Node],Node,[Node])
type UDecomp      = (Maybe UContext,UGraph)


-- local
--
type Context' a b = (Adj b,a,Adj b)
type GraphRep a b = FiniteMap Node (Context' a b)


----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------


-- pretty printing
--
showsGraph :: (Show a,Show b) => GraphRep a b -> ShowS
showsGraph Empty = id
showsGraph (Node l (v,(_,lab,suc)) r) = showsGraph l . ('\n':) . 
     shows v . (':':) . shows lab . ("->"++) . shows suc . showsGraph r
                
instance (Show a,Show b) => Show (Graph a b) where
  showsPrec _ (Graph g) = showsGraph g


-- other
--
addSucc v l (pre,lab,suc) = (pre,lab,(l,v):suc)
addPred v l (pre,lab,suc) = ((l,v):pre,lab,suc)

clearSucc v l (pre,lab,suc) = (pre,lab,filter ((/=v).snd) suc)
clearPred v l (pre,lab,suc) = (filter ((/=v).snd) pre,lab,suc)

updAdj :: GraphRep a b -> Adj b -> (b -> Context' a b -> Context' a b) -> GraphRep a b
updAdj g []         f              = g
updAdj g ((l,v):vs) f | elemFM g v = updAdj (updFM g v (f l)) vs f
                      | otherwise  = error ("Edge Exception, Node: "++show v)

-- pairL x ys = map ((,) x) ys
-- pairR x ys = map (flip (,) x) ys
fst4 (x,_,_,_) = x
snd4 (_,x,_,_) = x
thd4 (_,_,x,_) = x
fth4 (_,_,_,x) = x

-- some (un)labeling functions
-- 
labUEdges = map (\(v,w)->(v,w,()))
labUNodes = map (\v->(v,()))
labUAdj   = map (\v->((),v))
unlabEdges = map (\(v,w,_)->(v,w))
unlabNodes = map fst
unlabAdj   = map snd


----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------


-- constructing graphs
--
empty :: Graph a b 
empty =  Graph emptyFM

isEmpty :: Graph a b -> Bool
isEmpty (Graph g) = case g of {Empty -> True; _ -> False}

embed :: Context a b -> Graph a b -> Graph a b 
embed (pre,v,l,suc) (Graph g) | elemFM g v = error ("Node Exception, Node: "++show v)
                              | otherwise  = Graph g3
      where g1 = addToFM g v (pre,l,suc)
            g2 = updAdj g1 pre (addSucc v)
            g3 = updAdj g2 suc (addPred v)         

infixr &
c & g = embed c g


-- decomposing graphs
--
match :: Node -> Graph a b -> Decomp a b
match v (Graph g) = 
      case splitFM g v of 
           Nothing -> (Nothing,Graph g)
           Just (g,(_,(pre,lab,suc))) -> (Just (pre',v,lab,suc),Graph g2)
                where suc' = filter ((/=v).snd) suc
                      pre' = filter ((/=v).snd) pre
                      g1   = updAdj g  suc' (clearPred v)
                      g2   = updAdj g1 pre' (clearSucc v)

-- the same for unlabeled graphs
--
emptyU :: UGraph
emptyU = empty

embedU :: UContext -> UGraph -> UGraph
embedU (p,v,s) = embed (labUAdj p,v,(),labUAdj s)

matchU :: Node -> UGraph -> UDecomp
matchU v g = case match v g of
               (Nothing,g')        -> (Nothing,g')
               (Just (p,v,_,s),g') -> (Just (unlabAdj p,v,unlabAdj s),g')

matchAnyU :: UGraph -> (UContext,UGraph)
matchAnyU g = ((unlabAdj p,v,unlabAdj s),g') where ((p,v,_,s),g') = matchAny g

{-
-- Note that with

membed :: Decomp a b -> Graph a b
membed (Nothing,g) = g
membed (Just c, g) = embed c g

-- and

gid :: Node -> Graph a b -> Graph a b
gid v = membed . match v

-- we have that gid is an identity on graphs for any node v.
-}


-- derived/specialized decompositions
--
-- match      matches a specified node (regards loops as successors)
-- matchP     matches a specified node (regards loops as predecessors)
-- matchAny   matches an arbitrary node
-- matchSome  matches any node with a specified property
-- matchThe   matches a node if it is uniquely characterized by the given property
--
matchP :: Node -> Graph a b -> Decomp a b
matchP v (Graph g) = 
       case splitFM g v of 
            Nothing -> (Nothing,Graph g)
            Just (g,(_,(pre,lab,suc))) -> (Just (pre,v,lab,suc'),Graph g2)
                 where suc' = filter ((/=v).snd) suc
                       pre' = filter ((/=v).snd) pre
                       g1   = updAdj g  suc' (clearPred v)
                       g2   = updAdj g1 pre' (clearSucc v)

matchAny :: Graph a b -> GDecomp a b
matchAny (Graph Empty)              = error "Match Exception, Empty Graph"
matchAny g@(Graph (Node _ (v,_) _)) = (c,g') where (Just c,g') = match v g

matchSome :: (Graph a b -> Node -> Bool) -> Graph a b -> GDecomp a b
matchSome _ (Graph Empty) = error "Match Exception, Empty Graph"
matchSome p g = case filter (p g) (nodes g) of
                  []      ->  error "Match Exception, no such node found"
                  (v:vs)  ->  (c,g') where (Just c,g') = match v g

matchThe :: (Graph a b -> Node -> Bool) -> Graph a b -> GDecomp a b
matchThe _ (Graph Empty) = error "Match Exception, Empty Graph"
matchThe p g = case filter (p g) (nodes g) of
                  []   ->  error "Match Exception, no such node found"
                  [v]  ->  (c,g') where (Just c,g') = match v g
                  _    ->  error "Match Exception, more than one node found"


-- decompositions ignoring remaining graph
--
context :: Node -> Graph a b -> Context a b
context v (Graph g) = 
        case lookupFM g v of 
             Nothing            -> error ("Match Exception, Node: "++show v)
             Just (pre,lab,suc) -> (filter ((/=v).snd) pre,v,lab,suc)

contextP :: Node -> Graph a b -> Context a b
contextP v (Graph g) = 
         case lookupFM g v of 
              Nothing            -> error ("Match Exception, Node: "++show v)
              Just (pre,lab,suc) -> (pre,v,lab,filter ((/=v).snd) suc)


----------------------------------------------------------------------
-- TYPE CLASSES
----------------------------------------------------------------------

-- newtype XNode a = X (LNode a)
-- type LNodes a = [LNode a]
-- 
-- class Label a l b where
--   label   :: a -> l -> b
--   unlabel :: l -> a
-- 
-- instance Lab Node (LNode b) b where
--   label   v l   = (v,l)
--   unlabel (v,_) = v
-- 
-- instance Lab [Node] LNodes where
--   label vs l = zip vs (repeat l)
--   unlabel    = map fst
-- 
-- instance Lab Edge LEdge where
--   label (v,w) l   = (v,w,l)
--   unlabel (v,w,_) = (v,w)
-- 
-- instance Lab Node LNode where
--   label v l     = (v,l)
--   unlabel (v,_) = v


-- class Insert a b c where
--   ins :: c -> Graph a b -> Graph a b
-- 
-- instance Insert () b Node      where ins g v = insNode g (v,())
-- instance Insert a  b (LNode a) where ins = insNode
-- instance Insert a  b [LNode a] where ins = insNodes
-- instance Insert a  b (LEdge b) where ins = insEdge
-- instance Insert a  b [LEdge b] where ins = insEdges


-- decompositions ignoring contexts
--
delNode :: Node -> Graph a b -> Graph a b
delNode v = delNodes [v]

delNodes :: [Node] -> Graph a b -> Graph a b
delNodes []     g = g
delNodes (v:vs) g = delNodes vs (snd (match v g))

delEdge :: Edge -> Graph a b -> Graph a b
delEdge (v,w) g = case match v g of
                    (Nothing,_)        -> g
                    (Just (p,v,l,s),g) -> embed (p,v,l,filter ((/=w).snd) s) g

delEdges :: [Edge] -> Graph a b -> Graph a b
delEdges es g = foldr delEdge g es 
 

-- projecting on context elements
--
context1 v g = fst4 (contextP v g)
context2 v g = snd4 (context v g)
context3 v g = thd4 (context v g)
context4 v g = fth4 (context v g)


-- informations derived from specific contexts
--
suc :: Graph a b -> Node -> [Node]
suc g v = map snd (context4 v g)

pre :: Graph a b -> Node -> [Node] 
pre g v = map snd (context1 v g)

neighbors :: Graph a b -> Node -> [Node] 
neighbors g v = (\(p,_,_,s) -> map snd (p++s)) (context v g)

out :: Graph a b -> Node -> [LEdge b] 
out g v = map (\(l,w)->(v,w,l)) (context4 v g)

inn :: Graph a b -> Node -> [LEdge b] 
inn g v = map (\(l,w)->(w,v,l)) (context1 v g)

outdeg :: Graph a b -> Node -> Int
outdeg g v = length (context4 v g)

indeg :: Graph a b -> Node -> Int
indeg g v = length (context1 v g)

deg :: Graph a b -> Node -> Int
deg g v = (\(p,_,_,s) -> length p+length s) (context v g)


-- above operations for already given contexts
--
suc' :: Context a b -> [Node]
suc' (_,_,_,s) = map snd s

pre' :: Context a b -> [Node] 
pre' (p,_,_,_) = map snd p

neighbors' :: Context a b -> [Node] 
neighbors' (p,_,_,s) = map snd p++map snd s

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

node' :: Context a b -> Node
node' (_,v,_,_) = v

lab' :: Context a b -> a
lab' (_,_,l,_) = l

labNode' :: Context a b -> LNode a
labNode' (_,v,l,_) = (v,l)


-- gobal projections/selections
--
noNodes :: Graph a b -> Int
noNodes (Graph g) = sizeFM g

nodeRange :: Graph a b -> (Node,Node)
nodeRange (Graph Empty) = (0,-1)
nodeRange (Graph g)     = (ix (minFM g),ix (maxFM g)) where ix = fst.fromJust

nodes :: Graph a b -> [Node]
nodes (Graph g) = (map fst (fmToList g))

labNodes :: Graph a b -> [LNode a]
labNodes (Graph g) = map (\(v,(_,l,_))->(v,l)) (fmToList g)

edges :: Graph a b -> [Edge]
edges (Graph g) = concatMap (\(v,(_,_,s))->map (\(_,w)->(v,w)) s) (fmToList g)

labEdges :: Graph a b -> [LEdge b]
labEdges (Graph g) = concatMap (\(v,(_,_,s))->map (\(l,w)->(v,w,l)) s) (fmToList g)
            

-- some utilities to build graphs
--
newNodes :: Int -> Graph a b -> [Node]
newNodes i g = [n..n+i] where n = 1+foldr max 0 (nodes g)

insNode :: LNode a -> Graph a b -> Graph a b
insNode (v,l) = embed ([],v,l,[])

insNodes :: [LNode a] -> Graph a b -> Graph a b
insNodes vs g = foldr insNode g vs 

insEdge :: LEdge b -> Graph a b -> Graph a b
insEdge (v,w,l) g = embed (pre,v,lab,(l,w):suc) g'
                    where (Just (pre,_,lab,suc),g') = match v g

insEdges :: [LEdge b] -> Graph a b -> Graph a b
insEdges es g = foldr insEdge g es
 
mkGraph :: [LNode a] -> [LEdge b] -> Graph a b
mkGraph vs es = (insEdges es . insNodes vs) empty

mkUGraph :: [Node] -> [Edge] -> UGraph
mkUGraph vs es = mkGraph (labUNodes vs) (labUEdges es) 

buildGr :: [Context a b] -> Graph a b
buildGr = foldr embed empty


