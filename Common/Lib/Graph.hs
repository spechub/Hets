
{- |
Module      :  $Header$
Copyright   :  (c) 2000 by Martin Erwig
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
    Inductive Graphs. The implementation is based on extensible finite maps.
-}

module Common.Lib.Graph (
-- types
   Node,LNode,UNode,                  -- plain, labeled, and unit-labeled node
   Edge,LEdge,UEdge,                  -- plain, labeled, and unit-labeled edge
   Graph,UGraph,                      -- plain and unit-labeled graph
   Adj,Context,MContext,Decomp,GDecomp,     -- inductive graph view
   Path,LPath,UPath,                  -- plain, labeled, and unit-labeled path
-- main functions
   empty,embed,(&),match,matchP,matchAny,
   emptyU,embedU,matchU,matchAnyU,
-- derived operations
   isEmpty,matchSome,matchThe,context,contextP,
   delNode,delNodes,delEdge,delEdges,
   delLEdge,
   suc,pre,neighbors,out,inn,indeg,outdeg,deg,
   suc',pre',neighbors',out',inn',indeg',outdeg',deg',node',lab',labNode',
   noNodes,nodeRange,nodes,labNodes,edges,labEdges,
   -- graph folds
   --    ufold,gfold,  --> see Basic.hs
   -- graph transformations
   --    undir, gmap,  --> see Basic.hs
-- utilities to for (un)labeling
   labUEdges,labUNodes,labUAdj,
   unlabEdges,unlabNodes,unlabAdj,
-- utilities to build graphs
   newNodes,insNode,insNodes,insEdge,insEdges,insEdgeNub,
   mkGraph,mkUGraph,buildGr
) where

import Common.Lib.SimpleMap
import Data.Maybe (fromJust)
import Data.List(sortBy)

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

-- added for checking consistent ATerm files
instance (Eq a, Eq b) => Eq (Graph a b) where
    x == y = sortBy nodeOrd (labNodes x) == sortBy nodeOrd (labNodes y)
             && sortBy edgeOrd (labEdges x) == sortBy edgeOrd (labEdges y)
        where nodeOrd (n1,_) (n2,_) = n1 `compare` n2
              edgeOrd (s1,t1,_) (s2,t2,_) = (s1,t1) `compare` (s2,t2)

type Path      = [Node]
type LPath a   = [LNode a]
type UPath     = [UNode]


-- types supporting inductive graph view
--
type Adj b        = [(b,Node)]
type Context a b  = (Adj b,Node,a,Adj b) 
              -- Context a b "=" Context' a b "+" Node
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
showsGraph m = case minFM m of 
                 Just (v, (_,lab,s)) -> 
                  ('\n':) . shows v . (':':) . 
                          shows lab . ("->"++) . shows s .    
                          showsGraph (delFromFM m v)
                 Nothing -> id
                
instance (Show a,Show b) => Show (Graph a b) where
  showsPrec _ (Graph g) = showsGraph g


-- other
--
addSucc, addPred, clearSucc, clearPred 
    :: Node -> b -> Context' a b -> Context' a b 
addSucc v l (p,lab,s) = (p, lab, (l,v) : s)
addPred v l (p,lab,s) = ((l,v) : p, lab, s)
clearSucc v _l (p,lab,s) = (p,lab,filter ((/=v).snd) s)
clearPred v _l (p,lab,s) = (filter ((/=v).snd) p,lab,s)

updAdj :: GraphRep a b -> Adj b -> (b -> Context' a b -> Context' a b) 
       -> GraphRep a b
updAdj g []         _f             = g
updAdj g ((l,v):vs) f | elemFM g v = updAdj (updFM g v (f l)) vs f
                      | otherwise  = error ("Edge Exception, Node: "++show v)

-- some (un)labeling functions
-- 
labUEdges :: [(a, b)] -> [(a, b, ())]
labUEdges = map (\(v,w)->(v,w,()))
labUNodes :: [a] -> [(a, ())]
labUNodes = map (\v->(v,()))
labUAdj    :: [a] -> [((), a)]
labUAdj    = map (\v->((),v))
unlabEdges :: [(a, b, c)] -> [(a, b)]
unlabEdges = map (\(v,w,_)->(v,w))
unlabNodes :: [(a, b)] -> [a]
unlabNodes = map fst
unlabAdj   :: [(a, b)] -> [b]
unlabAdj   = map snd

----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------


-- constructing graphs
--
empty :: Graph a b 
empty =  Graph emptyFM

isEmpty :: Graph a b -> Bool
isEmpty (Graph g) = isEmptyFM g

embed :: Context a b -> Graph a b -> Graph a b 
embed (p,v,l,s) (Graph g) | elemFM g v = error 
                                         ("Node Exception, Node: "++show v)
                          | otherwise  = Graph g3
      where g1 = addToFM g v (p,l,s)
            g2 = updAdj g1 p (addSucc v)
            g3 = updAdj g2 s (addPred v)         

infixr &
(&) :: Context a b -> Graph a b -> Graph a b 
c & g = embed c g


-- decomposing graphs
--
match :: Node -> Graph a b -> Decomp a b
match v (Graph g) = 
      case splitFM g v of 
           Nothing -> (Nothing,Graph g)
           Just (g',(_,(p,lab,s))) -> (Just (p',v,lab,s),Graph g2)
                where s' = filter ((/=v).snd) s
                      p' = filter ((/=v).snd) p
                      g1   = updAdj g' s' (clearPred v)
                      g2   = updAdj g1 p' (clearSucc v)

-- the same for unlabeled graphs
--
emptyU :: UGraph
emptyU = empty

embedU :: UContext -> UGraph -> UGraph
embedU (p,v,s) = embed (labUAdj p,v,(),labUAdj s)

matchU :: Node -> UGraph -> UDecomp
matchU v g = case match v g of
               (Nothing,g')        -> (Nothing,g')
               (Just (p,v',_,s),g') -> (Just (unlabAdj p,v',unlabAdj s),g')

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
-- matchThe   matches a node if it uniquely has the given property
--
matchP :: Node -> Graph a b -> Decomp a b
matchP v (Graph g) = 
       case splitFM g v of 
            Nothing -> (Nothing,Graph g)
            Just (g',(_,(p,lab,s))) -> (Just (p,v,lab,s'),Graph g2)
                 where s' = filter ((/=v).snd) s
                       p' = filter ((/=v).snd) p
                       g1   = updAdj g'  s' (clearPred v)
                       g2   = updAdj g1 p' (clearSucc v)

matchAny :: Graph a b -> GDecomp a b
matchAny g@(Graph m) = case minFM m of 
    Nothing -> error "Match Exception, Empty Graph"
    Just (v, _) -> case match v g of 
        (Just c, g') -> (c, g')
        _ -> error "matchAny"

matchSome :: (Graph a b -> Node -> Bool) -> Graph a b -> GDecomp a b
matchSome p g = case filter (p g) (nodes g) of
                  []      ->  error "Match Exception, no such node found"
                  (v:_)   ->  (c,g') where (Just c,g') = match v g

matchThe :: (Graph a b -> Node -> Bool) -> Graph a b -> GDecomp a b
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
             Just (p,lab,s)     -> (filter ((/=v).snd) p,v,lab,s)

contextP :: Node -> Graph a b -> Context a b
contextP v (Graph g) = 
         case lookupFM g v of 
              Nothing            -> error ("Match Exception, Node: "++show v)
              Just (p,lab,s) -> (p,v,lab,filter ((/=v).snd) s)

-- decompositions ignoring contexts
--
delNode :: Node -> Graph a b -> Graph a b
delNode v = delNodes [v]

delNodes :: [Node] -> Graph a b -> Graph a b
delNodes []     g = g
delNodes (v:vs) g = delNodes vs (snd (match v g))

delEdge :: Edge -> Graph a b -> Graph a b
delEdge (v,w) g = case match v g of
    (Nothing,_)          -> g
    (Just (p,v',l,s),g') -> embed (p,v',l,filter ((/=w).snd) s) g'

delLEdge :: Eq b => LEdge b -> Graph a b -> Graph a b
delLEdge (v,w,lab) g = case match v g of
    (Nothing,_)          -> error "delLEdge did not work"
    (Just (p,v',l,s),g') -> embed (p,v',l,filter((/=(lab,w))) s) g'


delEdges :: [Edge] -> Graph a b -> Graph a b
delEdges es g = foldr delEdge g es 
 

-- projecting on context elements
--
context1, context4 :: Node -> Graph a b -> Adj b
context1 v g = fst4 (contextP v g) where fst4 (x,_,_,_) = x
context4 v g = fth4 (context v g) where fth4 (_,_,_,x) = x

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
nodeRange (Graph g)     = if isEmptyFM g then (0, -1) else 
                          (ix (minFM g),ix (maxFM g)) where ix = fst.fromJust

nodes :: Graph a b -> [Node]
nodes (Graph g) = (map fst (fmToList g))

labNodes :: Graph a b -> [LNode a]
labNodes (Graph g) = map (\(v,(_,l,_))->(v,l)) (fmToList g)

edges :: Graph a b -> [Edge]
edges (Graph g) = concatMap (\(v,(_,_,s))->map (\(_,w)->(v,w)) s) (fmToList g)

labEdges :: Graph a b -> [LEdge b]
labEdges (Graph g) = 
    concatMap (\(v,(_,_,s))->map (\(l,w)->(v,w,l)) s) (fmToList g)
            

-- some utilities to build graphs
--
newNodes :: Int -> Graph a b -> [Node]
newNodes i g = [n..n+i] where n = 1+foldr max 0 (nodes g)

insNode :: LNode a -> Graph a b -> Graph a b
insNode (v,l) = embed ([],v,l,[])

insNodes :: [LNode a] -> Graph a b -> Graph a b
insNodes vs g = foldr insNode g vs 

insEdge :: LEdge b -> Graph a b -> Graph a b
insEdge (v,w,l) g = embed (p,v,lab,(l,w):s) g'
                    where (Just (p,_,lab,s),g') = match v g

insEdges :: [LEdge b] -> Graph a b -> Graph a b
insEdges es g = foldr insEdge g es

-- | insert edge only if not already present
insEdgeNub :: Eq b => LEdge b -> Graph a b -> Graph a b
insEdgeNub (v,w,l) g = 
   if (l,w) `elem` s then g
      else embed (p,v,lab,(l,w):s) g'
   where (Just (p,_,lab,s),g') = match v g

 
mkGraph :: [LNode a] -> [LEdge b] -> Graph a b
mkGraph vs es = (insEdges es . insNodes vs) empty

mkUGraph :: [Node] -> [Edge] -> UGraph
mkUGraph vs es = mkGraph (labUNodes vs) (labUEdges es) 

buildGr :: [Context a b] -> Graph a b
buildGr = foldr embed empty
