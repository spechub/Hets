module Map where

map1 :: (a -> b) -> [a] -> [b]
map1 f [] = []
map1 f (x:xs) = f x ++ map1 f xs

{-# AXIOMS
         "map1" forall f g xs ->  map1 f (map1 g xs) = map1 (f.g) xs
#-}
