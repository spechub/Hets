-- (c) 2000 by Martin Erwig
-- | Inward directed trees as lists of paths.
module Data.Graph.Inductive.Aux.RootPath (
    -- * Types
    RTree,LRTree,
    -- * Operations
    getPath,getLPath,
    getDistance
) where

import Data.Graph.Inductive.Graph

-- newtype LNode a = LN (a,Node) 
--         deriving Show
-- 
-- type LPath a = [LNode a]

instance Eq a => Eq (LPath a) where
  []	    == []	 = True
  ((_,x):_) == ((_,y):_) = x==y
  _	    == _	 = False

instance Ord a => Ord (LPath a) where
  compare [] []		      = EQ
  compare ((_,x):_) ((_,y):_) = compare x y
  compare _ _		      = error "LPath: cannot compare to empty path"
--  ((_,x):_) < ((_,y):_) = x<y

--------

type LRTree a = [LPath a]
type RTree = [Path]

first :: ([a] -> Bool) -> [[a]] -> [a]
first _ [[]] = []
first p xss  = case filter p xss of
                 []   -> []
                 x:_  -> x

getPath :: Node -> RTree -> Path
getPath v = reverse . first (\(w:_)->w==v) 

getLPath :: Node -> LRTree a -> LPath a
getLPath v = reverse . first (\((w,_):_)->w==v)

getDistance :: Node -> LRTree a -> a
getDistance v = snd . head . first (\((w,_):_)->w==v)

