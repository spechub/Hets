-- FacAndFibWithCases.hs
-- Output: 123

fac :: Int -> Int
fac = \n -> case n of
                 0 -> 1
                 1 -> 1
                 z -> n * fac (n - 1) 

fib :: Int -> Int
fib = \h -> case h of
                 0 -> 1
                 1 -> 1
                 u -> (fib (u - 1)) + (fib (u - 2))

main :: Int
main = fac 5 + fib 3
