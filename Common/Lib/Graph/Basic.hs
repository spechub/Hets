------------------------------------------------------------------------------
--
--  Basic.hs -- Basic Graph Algorithms
--
--  (c) 1999 - 2002 by Martin Erwig [see file COPYRIGHT]
--
------------------------------------------------------------------------------


module Basic
(
   grev,
   undir,unlab,
   gsel,efilter,elfilter,
   hasLoop,isSimple, 
   gfold
) 
where


import Graph

import Thread (threadMaybe,threadList)
import List (nub)


----------------------------------------------------------------------
-- SIMPLE ALGORITHMS
----------------------------------------------------------------------


grev :: DynGraph gr => gr a b -> gr a b 
grev = gmap (\(p,v,l,s)->(s,v,l,p))

undir :: (Eq b,DynGraph gr) => gr a b -> gr a b
undir = gmap (\(p,v,l,s)->let ps = nub (p++s) in (ps,v,l,ps))
-- this version of undir considers edge lables and keeps edges with
-- different labels, an alternative is the definition below:
--   undir = gmap (\(p,v,l,s)->
--           let ps = nubBy (\x y->snd x==snd y) (p++s) in (ps,v,l,ps))


unlab :: DynGraph gr => gr a b -> gr () ()
unlab = gmap (\(p,v,_,s)->(unlabAdj p,v,(),unlabAdj s))
        where unlabAdj = map (\(_,v)->((),v))
-- alternative:
--    unlab = nmap (\_->()) . emap (\_->())
            
gsel :: Graph gr => (Context a b -> Bool) -> gr a b -> [Context a b]
gsel p = ufold (\c cs->if p c then c:cs else cs) []


-- filter operations
--
-- efilter  : filter based on edge property
-- elfilter : filter based on edge label property
--
efilter :: DynGraph gr => (LEdge b -> Bool) -> gr a b -> gr a b
efilter f = ufold cfilter empty
            where cfilter (p,v,l,s) g = (p',v,l,s') & g
                   where p' = filter (\(b,u)->f (u,v,b)) p
                         s' = filter (\(b,w)->f (v,w,b)) s

elfilter :: DynGraph gr => (b -> Bool) -> gr a b -> gr a b
elfilter f = efilter (\(_,_,b)->f b)


-- some predicates and classifications
--
hasLoop :: Graph gr => gr a b -> Bool
hasLoop = not . null . (gsel (\c->(node' c `elem` suc' c)))

isSimple :: Graph gr => gr a b -> Bool
isSimple = not . hasLoop


-- directed graph fold
--
threadGraph f c = threadMaybe f c match

-- gfold1 f d b u = threadGraph (\c->d (labNode' c)) (\c->gfoldn f d b u (f c))
gfold1 f d b = threadGraph d (\c->gfoldn f d b (f c))
gfoldn f d b = threadList b (gfold1 f d b)

-- gfold :: ((Context a b) -> [Node]) -> ((Node,a) -> c -> d) -> 
--          (Maybe d -> c -> c) -> c -> [Node] -> Graph a b -> c
-- gfold f d b u l g = fst (gfoldn f d b u l g)

-- type Dir a b    = (Context a b) -> [Node]  -- direction of fold
-- type Dagg a b c = (Node,a) -> b -> c       -- depth aggregation
-- type Bagg a b   = (Maybe a -> b -> b,b)    -- breadth/level aggregation
-- 
-- gfold :: (Dir a b) -> (Dagg a c d) -> (Bagg d c) -> [Node] -> Graph a b -> c
-- gfold f d (b,u) l g = fst (gfoldn f d b u l g)

type Dir a b      = (Context a b) -> [Node]  -- direction of fold
type Dagg a b c d = (Context a b) -> c -> d  -- depth aggregation
type Bagg a b     = (Maybe a -> b -> b,b)    -- breadth/level aggregation

gfold :: Graph gr => 
         (Dir a b) -> (Dagg a b c d) -> (Bagg d c) -> [Node] -> gr a b -> c
gfold f d b l g = fst (gfoldn f d b l g)


 
-- not finished yet ...
--
-- undirBy :: (b -> b -> b) -> Graph a b -> Graph a b
-- undirBy = gmap (\(p,v,l,s)->let ps = nub (p++s) in (ps,v,l,ps))

