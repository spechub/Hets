-- HoDatTypes.hs
-- Output: 12

data F a b = N | Fn (a -> b)

-- weird :: F a b -> a -> b
weird N x = error "ouch"
weird (Fn f) x = f x

inc :: Int -> Int
inc x = x + 1

addThree :: Int -> Int -> Int -> Int
addThree a b c = a + b + c

main :: Int
main = (weird (Fn inc) 5) + (weird (Fn addThree) 1 2 3)
