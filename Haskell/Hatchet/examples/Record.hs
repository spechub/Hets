-- Record.hs
-- Output: (Z{re=3.0,im=2.0},8.0,-3.0)

data Complex = Z {re, im :: Float}
               deriving Show

main :: (Complex, Float, Float)
main = (conjugate (Z 3 (-2)), abso w + re w, toReal (Z (-3) 4))
       where
       w = Z 3 4

conjugate :: Complex -> Complex
conjugate z = Z (re z) (-(im z))

abso :: Complex -> Float
abso z = sqrt ((re z)*(re z) + (im z)*(im z))

-- this function breaks the parser
-- setImToOne z = z {im = 1}

toReal :: Complex -> Float
-- toReal (Z {re = r}) = r
toReal = re
