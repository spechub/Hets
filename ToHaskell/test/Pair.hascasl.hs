module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data A_a = A_a
         deriving (Show, Eq, Ord)
 
data A_b = A_b
         deriving (Show, Eq, Ord)
 
f :: (A_a, A_b) -> Pair
 
a_fst :: Pair -> A_a
 
g :: Pair -> A_a
 
a_snd :: Pair -> A_b
a_fst (Pair (x_11_11, x_11_12)) = x_11_11
a_snd (Pair (x_11_11, x_11_12)) = x_11_12
 
data Pair = Pair !(A_a, A_b)
          deriving (Show, Eq, Ord)
f (a, b) = Pair (a, b)
g (Pair (a, b)) = a
