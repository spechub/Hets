-- Id.hs
-- Output: 7

-- main :: Int
main = myid ((myid myid) (myid 7))
     where
     -- myid :: a -> a
     myid = \x -> x


