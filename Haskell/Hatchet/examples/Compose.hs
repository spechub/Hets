-- Compose.hs
-- Output: 9

main :: Int
main = (compose head tail functionList) 4

inc :: Int -> Int
inc = \x -> x + 1

double :: Int -> Int
double = \y -> y * 2

functionList :: [Int->Int]
functionList = [inc,compose inc double,double]

compose :: (b -> c) -> (a -> b) -> a -> c
compose = \m -> \n -> \o -> m (n o)
