--
--  Basic.hs -- Basic Graph Algorithms  (c) 2000 by Martin Erwig
--
--
module Basic (
   gmap,nmap,emap,               -- basic operations
   grev,                   
   undir,unlab,
   gsel,hasLoop,isSimple, 
   ufold,gfold,                  -- graph folds
) where


import Graph
import Thread (threadMaybe,threadList)
import List (nub,nubBy)


----------------------------------------------------------------------
-- SIMPLE ALGORITHMS
----------------------------------------------------------------------

gmap :: (Context a b -> Context c d) -> Graph a b -> Graph c d
gmap f = ufold (\c->(f c&)) empty
-- alternative:
--   gmap f = ufold (\c g->embed (f c) g) empty

nmap :: (a -> c) -> Graph a b -> Graph c b
nmap f = gmap (\(p,v,l,s)->(p,v,f l,s))

emap :: (b -> c) -> Graph a b -> Graph a c
emap f = gmap (\(p,v,l,s)->(map1 f p,v,l,map1 f s))
         where map1 f = map (\(l,v)->(f l,v))

grev :: Graph a b -> Graph a b 
grev = gmap (\(p,v,l,s)->(s,v,l,p))

undir :: Graph a b -> Graph a b
undir = gmap (\(p,v,l,s)->let ps = nubBy (\x y->snd x==snd y) (p++s) in (ps,v,l,ps))
 
unlab :: Graph a b -> UGraph
unlab = gmap (\(p,v,_,s)->(unlabAdj p,v,(),unlabAdj s))
        where unlabAdj = map (\(_,v)->((),v))
-- alternative:
--    unlab = nmap (\_->()) . emap (\_->())
            
gsel :: (Context a b -> Bool) -> Graph a b -> [Context a b]
gsel p = ufold (\c cs->if p c then c:cs else cs) []


-- some predicates and classifications
--
hasLoop :: Graph a b -> Bool
hasLoop = not . null . (gsel (\c->(node' c `elem` suc' c)))

isSimple :: Graph a b -> Bool
isSimple = not . hasLoop


-- graph folds
--
ufold :: ((Context a b) -> c -> c) -> c -> Graph a b -> c
ufold f u g | isEmpty g = u
            | otherwise = f c (ufold f u g') 
            where (c,g') = matchAny g

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

gfold :: (Dir a b) -> (Dagg a b c d) -> (Bagg d c) -> [Node] -> Graph a b -> c
gfold f d b l g = fst (gfoldn f d b l g)




-- direct implementation of gmap and grev
--
-- gmap'  :: (Context a b -> Context c d) -> Graph a b -> Graph c d
-- gmap' f g | isEmpty g = empty
--           | otherwise = f c & gmap f g' where (c,g') = matchAny g
-- 
-- grev'  :: Graph a b -> Graph a b
-- grev' g | isEmpty g = empty
--         | otherwise = (s,v,l,p) & grev g' where ((p,v,l,s),g') = matchAny g

-- nmap realized through ufold
--
-- nmap :: (a -> c) -> Graph a b -> Graph c b
-- nmap f = ufold (\(p,v,l,s)->((p,v,f l,s)&)) empty

-- implementation of nodes by ufold
--
-- nodes :: Graph a b -> [Node]
-- nodes = ufold (\(p,v,l,s)->(v:)) []
 
-- not finished yet ...
--
-- undirBy :: (b -> b -> b) -> Graph a b -> Graph a b
-- undirBy = gmap (\(p,v,l,s)->let ps = nub (p++s) in (ps,v,l,ps))

