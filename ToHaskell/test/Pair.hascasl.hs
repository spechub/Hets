module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data Pair = Pair !(A_a, A_b)
          deriving (Show, Eq, Ord)
 
data A_a = A_a
         deriving (Show, Eq, Ord)
 
data A_b = A_b
         deriving (Show, Eq, Ord)
 
f :: (A_a, A_b) -> Pair
f = undefined
 
a_fst :: Pair -> A_a
a_fst = undefined
 
g :: Pair -> A_a
g = undefined
 
a_snd :: Pair -> A_b
a_snd = undefined
