module Map where

map1 :: (a -> b) -> [a] -> [b]
map1 f [] = []
map1 f (x:xs) = f x : map1 f xs

map2 :: (a -> b) -> [a] -> [b]
map2 f l = case l of
              [] -> []
              x:xs -> f x:map2 f xs


