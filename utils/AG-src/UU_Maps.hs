{- UU_AG
 - Copyright:  Arthur I. Baars
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {arthurb}@cs.uu.nl -}
module UU_Maps(emptyMap,singleMap,insert,insertComb,Map,locateMap
              ,map2list,list2map,contains,getKeys,getValues,delete) where

import UU_BinaryTrees
import Maybe
import List (sortBy)

newtype Map a b = Map (BinSearchTree (a,b))

emptyMap :: Map a b
emptyMap = Map Nil

-- construct a singleton map
singleMap :: key -> val -> Map key val
singleMap k v = Map (Node Nil (k,v) Nil)


-- locate a value in a map using a key
locateMap :: Ord key => key -> Map key val -> Maybe val
locateMap k (Map tree) = btFind compare tree k


contains :: Ord key => key -> Map key val -> Bool
contains k m = isJust (locateMap k m)

map2list :: Map key val -> [(key,val)]
map2list (Map tree) = toList' tree where
  toList' Nil          = []
  toList' (Node l x r) = toList' l ++ [x] ++ toList' r

list2map :: Ord key => [(key,val)] -> Map key val
list2map ls = foldr (uncurry insert) emptyMap ls

getKeys :: Map k v -> [k]
getKeys = map fst . map2list

getValues :: Map k v -> [v]
getValues = map snd . map2list

-- insert a binding into a map, overwrites old binding with the same key if it exists
insert :: Ord key => key -> val -> Map key val -> Map key val
insert = insertComb const

delete :: Ord k => k -> Map k v -> Map k v
delete key (Map tree) = Map (deleteTree compare key tree)

instance Functor (Map k) where
  fmap f (Map tree) =
   let mapTree Nil = Nil
       mapTree (Node l (k,v) r) = Node (mapTree l) (k,f v)(mapTree r)
   in Map (mapTree tree)




-- inserts a binding into a map; if there is already a binding the values of the old
-- and the new one are combined
insertComb :: Ord key => (val->val->val) -> key -> val -> Map key val -> Map key val
insertComb comb key val (Map tree) = Map (insertTree compare comb key val tree)


insertTree :: (key -> key -> Ordering)  -- comparator
           -> (val -> val -> val)       -- combine if already exists
           -> key
           -> val
           -> BinSearchTree (key,val)
           -> BinSearchTree (key,val)
insertTree comp comb k1 v1    =  ins where
     ins Nil                  =  Node Nil (k1,v1) Nil
     ins (Node l y@(k2,v2) r) =  case comp k1 k2 of
               LT             -> Node (ins l) y r
               EQ             -> Node l (k1,comb v1 v2) r
               GT             -> Node l y (ins r)


deleteTree :: (key -> key -> Ordering)  -- comparator
           -> key
           -> BinSearchTree (key,val)
           -> BinSearchTree (key,val)
deleteTree comp k1 tree       = del tree where
     del Nil                  = Nil
     del (Node l y@(k2,v2) r) =  case comp k1 k2 of
               LT             -> Node (del l) y r
               EQ             -> append l r
               GT             -> Node l y (del r)
     append Nil r = r
     append (Node a b c) r = Node a b (append c r)
instance (Show key,Show val) => Show (Map key val) where
    show m = show (map2list m)

{-

{-
 - inserts a value in a map
 -}
(<++) :: (Eq a,Show a) => (a,b) -> (b -> c) -> Map a c -> Map a c
(<++) pos@(i, n) f     (this@(key, val) : rest)
        | i == key    = trace ("\n Error discoverd in <++ :: entry: " ++ show i ++ " already exists!\n")  (this:rest)
        | otherwise   = this        : ((pos <++ f)  rest)
(<++) (i, n) f  [] = [(i, f n)]

{-
 - changes a value in a map
 -}
(<--) :: (Eq a,Show a) => a -> (b -> b) -> Map a b -> Map a b
(<--) i f          (this@(key, val) : rest)
        | i == key    = (i, (f val)):             rest
        | otherwise   = this        : ((i <-- f)  rest)
(<--) i f      []  = trace ("<-- :: entry: " ++ show i ++ " does not exist!\n") []

{-
 - changes or inserts a value in a map
 -}
(<+-) :: Eq a => (a,b) -> (b -> b) -> Map a b -> Map a b
(<+-) pos@(i, n) f     (this@(key, val) : rest)
        | i == key    = (i, (f val)):             rest
        | otherwise   = this        : ((pos <+- f)  rest)
(<+-) (i, n) f  [] = [(i, f n)]
  -}
