-- Tree.hs
-- Output: T 2 (T 1 Empty Empty) (T 3 Empty Empty)

data Btree a = Empty | T a (Btree a) (Btree a)
               deriving Show

buildtree :: Ord a => [a] -> Btree a
buildtree [] = Empty
buildtree (x:xs) = insert x (buildtree xs)

insert :: Ord a => a -> Btree a -> Btree a
insert val Empty = T val Empty Empty
insert val tree@(T tval left right)
   | val > tval = T tval left (insert val right)
   | otherwise = T tval (insert val left) right

main :: Btree Int
main = buildtree [3,1,2] 
