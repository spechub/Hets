module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data A__a = A__a
          deriving (Show, Eq, Ord)
 
data A__b = A__b
          deriving (Show, Eq, Ord)
 
f :: (A__a, A__b) -> Pair
 
a__fst :: Pair -> A__a
 
g :: Pair -> A__a
 
a__snd :: Pair -> A__b
g (Pair (a, b)) = a
f (a, b) = Pair (a, b)
 
data Pair = Pair !(A__a, A__b)
          deriving (Show, Eq, Ord)
a__snd (Pair (x_11_11, x_11_12)) = x_11_12
a__fst (Pair (x_11_11, x_11_12)) = x_11_11
