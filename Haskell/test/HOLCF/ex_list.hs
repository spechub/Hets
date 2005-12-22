

funOne :: Eq a => [a] -> [a] -> Bool
myMap :: [a] -> (a -> b) -> [b]

funOne x y = if x == (head x):(tail y) then True else False

myMap x f = case x of 
  [] -> []
  a:as -> (f a): myMap as f  

