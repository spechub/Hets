-- Map.hs
-- Output: ["HELLO","FLIBBLE"]

--mymap :: (a -> b) -> [a] -> [b]
mymap = \f -> \xs -> case xs of
                     [] -> [] 
                     (h:t) -> (f h) : (mymap f t) 

--main :: [[Char]]
main = mymap (mymap toUpper) ["hello","flibble"]
