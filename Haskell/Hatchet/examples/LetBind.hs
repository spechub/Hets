-- LetBind.hs
-- Output: 20

foo :: Int -> Int
foo = \y -> let 
             -- app :: (a -> b) -> a -> b
             app = \f x -> f x
             fun :: (a -> b) -> a -> b
             fun = let 
                     -- myid :: a -> a
                     myid = \x -> x
                     -- bar :: (a -> b) -> a -> b
                     bar = app 
                   in myid (let 
                              -- ram :: (a -> b) -> a -> b
                              ram = bar 
                              in ram
                           ) 
            in (fun plus 1 2) + (fun plus 1 2) 


plus :: Int -> Int -> Int
plus = \x y -> x + y

addThree :: Int -> Int -> Int -> Int
addThree = \a b c -> a + b + c

-- main :: Int
main = (foo 3) + (mysum ( mymap (\x -> 1 + x) [1,2,3]))

mymap :: (a -> b) -> [a] -> [b]
mymap = mymap 

mysum :: Num a => [a] -> a
mysum = mysum
