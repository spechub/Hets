--
--  Pairing Heaps
--

module Heap (
-- types
   Heap(..),
-- operations
   empty,unit,insert,merge,mergeAll,
   isEmpty,findMin,deleteMin,splitMin,
   build
) where


data Ord a => Heap a = Empty | Node a [Heap a]
     deriving Eq

showsHeap :: (Show a,Ord a) => Heap a -> ShowS
showsHeap Empty       = id
showsHeap (Node x []) = shows x
showsHeap (Node x hs) = shows x . (' ':) . shows hs
                
instance (Show a,Ord a) => Show (Heap a) where
  showsPrec _ d = showsHeap d


----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------

empty :: Ord a => Heap a
empty = Empty

unit :: Ord a => a -> Heap a
unit x = Node x []

insert :: Ord a => a -> Heap a -> Heap a
insert x h = merge (unit x) h

merge :: Ord a => Heap a -> Heap a -> Heap a 
merge h Empty = h
merge Empty h = h
merge h@(Node x hs) h'@(Node y hs') | x<y       = Node x (h':hs)
                                    | otherwise = Node y (h:hs')

mergeAll:: Ord a => [Heap a] -> Heap a 
mergeAll []        = Empty
mergeAll [h]       = h
mergeAll (h:h':hs) = merge (merge h h') (mergeAll hs)

isEmpty :: Ord a => Heap a -> Bool
isEmpty Empty = True
isEmpty _     = False
          
findMin :: Ord a => Heap a -> a
findMin Empty      = error "Heap.findMin: empty heap"
findMin (Node x _) = x

deleteMin :: Ord a => Heap a -> Heap a 
deleteMin Empty       = Empty
deleteMin (Node x hs) = mergeAll hs

splitMin :: Ord a => Heap a -> (a,Heap a)
splitMin Empty       = error "Heap.splitMin: empty heap"
splitMin (Node x hs) = (x,mergeAll hs)


----------------------------------------------------------------------
-- APPLICATION FUNCTIONS, EXAMPLES
----------------------------------------------------------------------


build :: Ord a => [a] -> Heap a 
build = foldr insert Empty

toList :: Ord a => Heap a -> [a]
toList Empty = []
toList h = x:toList r
           where (x,r) = (findMin h,deleteMin h)

heapsort :: Ord a => [a] -> [a]
heapsort = toList . build

l  = [6,9,2,13,6,8,14,9,10,7,5]
l' = reverse l

h1  = build l
h1' = build l'

s1  = heapsort l
s1' = heapsort l'

