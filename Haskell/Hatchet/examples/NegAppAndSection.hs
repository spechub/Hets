-- NegAppAndSection.hs
-- Output: []

main :: [Bool]
main = map (`elem` [4,5,6]) foo 

foo :: [Int]
foo = filter ((-3)>) [1..10]
