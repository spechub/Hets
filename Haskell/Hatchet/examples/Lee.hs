-- Lee.hs
-- Output: [4,6,8]

-- inc :: Prelude.Int -> Prelude.Int
inc x = x + 1

-- times :: Prelude.Int -> Prelude.Int -> Prelude.Int
times x y = x * y

-- double :: Prelude.Int -> Prelude.Int
double = times 2

--  di :: Prelude.Int -> Prelude.Int
di = mycompose double inc -- BUG: intention is inc.double

-- mycompose :: (a -> b) -> (c -> a) -> c -> b
mycompose f g x = f (g x)

-- mdi :: [Prelude.Int] -> [Prelude.Int]
mdi = map di


mymap :: (a -> b) -> [a] -> [b]
mymap f [] = []
mymap f list =  (f (head list)) : (mymap f (tail list))


-- main :: [Prelude.Int]
-- main = mdi [1,2,3]
main = print $ mdi [1,2,3]

-- main = print False
