module Common.ListUtils where

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x [] = []
splitBy x xs = let (l,rest) = break (==x) xs
                 in l : case rest of
                          []        -> []
                          (_:rest') -> splitBy x rest' 