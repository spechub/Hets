myfoldr :: (a -> b -> b) -> b -> [a] -> b
myfoldr = \f z xs -> foldrC (\x -> x) f z xs

foldrC :: (a -> b) -> (c -> a -> a) -> a -> [c] -> b
foldrC = \c f z l ->
          case l of
             [] -> c z
             (:) x xs -> foldrC (\n -> c (f x n)) f z xs

main = myfoldr (+) 0 [1,2,3] 
