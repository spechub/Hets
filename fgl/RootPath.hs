--
--  RootPath.hs -- Inward directed trees as lists of paths  (c) 2000 by Martin Erwig
--
module RootPath (
   RTree,LRTree,
   getPath,getLPath,
   getDistance
) where

import Graph

-- newtype LNode a = LN (a,Node) 
--         deriving Show
-- 
-- type LPath a = [LNode a]

instance Eq a => Eq (LPath a) where
  ((_,x):_) == ((_,y):_) = x==y

instance Ord a => Ord (LPath a) where
  ((_,x):_) < ((_,y):_) = x<y

--------

type LRTree a = [LPath a]
type RTree = [Path]

first :: (a -> Bool) -> [a] -> a
first p = head . filter p

getPath :: Node -> RTree -> Path
getPath v = reverse . first (\(w:_)->w==v) 

getLPath :: Node -> LRTree a -> LPath a
getLPath v = reverse .  first (\((w,_):_)->w==v)

getDistance :: Node -> LRTree a -> a
getDistance v = snd . head . first (\((w,_):_)->w==v)

