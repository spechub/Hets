-- RecursiveMain.hs


main :: Int -> Int
main = \x -> case x of
                1 -> 1 + main 0
                0 -> (app addthree 1 2 3) + (app inc 2)

app :: (a -> b) -> a -> b
app = \f x -> f x

inc :: Int -> Int
inc = \y -> y + 1

addthree :: Int -> Int -> Int -> Int
addthree = \a b c -> a + b + c
