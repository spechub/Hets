-- testing the use of explicit type 
-- annotations in the code

main :: IO ()
main = undefined

foo = (undefined :: Int)

zoo = let tuple = (True, (undefined :: [a])) in (snd tuple, fst tuple)

too = let tuple = (True, (undefined :: Either String ())) in (snd tuple, fst tuple)

yubyub = (3.0 ::  Floating a => a)


yowzer f = f ([]::Num a => [Maybe a])
