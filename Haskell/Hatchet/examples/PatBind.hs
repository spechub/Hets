-- PatBind.hs
-- Output: 7

main :: Int
main = foo 3

foo :: Int -> Int
foo x = h + t + (snd tup)
      where
      h :: Int
      t :: Int
      tup :: (Int,Int)
      tup@(h,t) = head $ zip [1..x] [3..15]
