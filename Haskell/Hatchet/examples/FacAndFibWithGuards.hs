-- FacAndfibWithGuards.hs
-- Output: 123

-- fac :: Int -> Int
fac n
   | n == 0 = 1
   | n == 1 = 1
   | otherwise = n * fac (n - 1)

-- fib :: Int -> Int
fib n 
   | n == 0 = 1
   | n == 1 = 1
   | otherwise = (fib (n - 1)) + (fib (n - 2))

-- main :: Int
main = fac 5 + fib 3
