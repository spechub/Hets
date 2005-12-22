
data Boolx = Minx | Plusx

data Natx a = Zx | Sx a | SSx (Natx a) Boolx

map1 :: Natx Int -> (Int -> Int) -> Natx Int
map1 x = \ f -> case x of 
       Zx -> Sx (f 0) 
       Sx n -> Sx (f n)
       SSx a t -> map2 a t f

map2 :: Natx Int -> Boolx -> (Int -> Int) -> Natx Int 
map2 x = \ w f -> case x of 
   Zx -> Zx
   Sx n -> Sx (n + 1) 
   SSx a t -> if t == Minx then SSx a w else map1 a f

