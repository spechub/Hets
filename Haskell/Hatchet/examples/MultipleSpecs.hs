-- MultipleSpecs.hs
-- Output: (10,9,'a',"hhhhhhh")

inc :: Int -> Int
inc = \x -> x + 1

times :: Int -> Int -> Int
times = \x -> \y -> x * y

double :: Int -> Int
double = times 2

doubleinc :: Int -> Int
doubleinc = mycompose double inc

incdouble :: Int -> Int
incdouble = mycompose inc double

myToLower :: Char -> Char
myToLower = mycompose toLower toUpper

replicateHead :: [Char] -> [Char]
replicateHead = mycompose (replicate 7) head

mycompose :: (a -> b) -> (c -> a) -> c -> b
mycompose = \f -> \g -> \x -> f (g x)

main :: (Int,Int,Char,[Char])
main = (doubleinc 4, incdouble 4, myToLower 'A', replicateHead "hello")
