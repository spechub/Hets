

fibon :: Int -> Int
fibon n = if n == 0 then 1 else if n == 1 then 1 else fibon (n - 1) + fibon (n - 2)


