------------------------------------------------------------------------------
--
--  TreeGraph.hs -- Dynamic Graphs  
--
--  (c) 1999 - 2002 by Martin Erwig [see file COPYRIGHT]
--
--  The implementation is based on extensible finite maps.
--  For a faster implementation of fixed size graphs, see IOArrGraph.hs
--
------------------------------------------------------------------------------

module TreeGraph (Gr,UGr) where


import Graph
import SimpleMap

import Maybe (fromJust)


----------------------------------------------------------------------
-- GRAPH REPRESENTATION
----------------------------------------------------------------------

data Gr a b = Gr (GraphRep a b)

type GraphRep a b = FiniteMap Node (Context' a b)
type Context' a b = (Adj b,a,Adj b)

type UGr = Gr () ()


----------------------------------------------------------------------
-- CLASS INSTANCES
----------------------------------------------------------------------


-- Show
--
showsGraph :: (Show a,Show b) => GraphRep a b -> ShowS
showsGraph Empty = id
showsGraph (Node _ l (v,(_,lab,suc)) r) = showsGraph l . ('\n':) . 
     shows v . (':':) . shows lab . ("->"++) . shows suc . showsGraph r
                
instance (Show a,Show b) => Show (Gr a b) where
  showsPrec _ (Gr g) = showsGraph g


-- Graph
-- 
instance Graph Gr where
  empty           = Gr emptyFM
  isEmpty (Gr g)  = case g of {Empty -> True; _ -> False}
  match           = matchGr
  mkGraph vs es   = (insEdges es . insNodes vs) empty
  labNodes (Gr g) = map (\(v,(_,l,_))->(v,l)) (fmToList g)
  -- more efficient versions of derived class members
  --
  matchAny (Gr Empty)                = error "Match Exception, Empty Graph"
  matchAny g@(Gr (Node _ _ (v,_) _)) = (c,g') where (Just c,g') = matchGr v g
  noNodes   (Gr g) = sizeFM g
  nodeRange (Gr Empty) = (0,0)
  nodeRange (Gr g)     = (ix (minFM g),ix (maxFM g)) where ix = fst.fromJust
  labEdges  (Gr g) = concatMap (\(v,(_,_,s))->map (\(l,w)->(v,w,l)) s) (fmToList g)


matchGr v (Gr g) = 
      case splitFM g v of 
           Nothing -> (Nothing,Gr g)
           Just (g,(_,(pre,lab,suc))) -> (Just (pre',v,lab,suc),Gr g2)
                where suc' = filter ((/=v).snd) suc
                      pre' = filter ((/=v).snd) pre
                      g1   = updAdj g  suc' (clearPred v)
                      g2   = updAdj g1 pre' (clearSucc v)


-- DynGraph
-- 
instance DynGraph Gr where
  (pre,v,l,suc) & (Gr g) | elemFM g v = error ("Node Exception, Node: "++show v)
                         | otherwise  = Gr g3
      where g1 = addToFM g v (pre,l,suc)
            g2 = updAdj g1 pre (addSucc v)
            g3 = updAdj g2 suc (addPred v)


----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------

addSucc v l (pre,lab,suc) = (pre,lab,(l,v):suc)
addPred v l (pre,lab,suc) = ((l,v):pre,lab,suc)

clearSucc v l (pre,lab,suc) = (pre,lab,filter ((/=v).snd) suc)
clearPred v l (pre,lab,suc) = (filter ((/=v).snd) pre,lab,suc)

updAdj :: GraphRep a b -> Adj b -> (b -> Context' a b -> Context' a b) -> GraphRep a b
updAdj g []         f              = g
updAdj g ((l,v):vs) f | elemFM g v = updAdj (updFM g v (f l)) vs f
                      | otherwise  = error ("Edge Exception, Node: "++show v)



