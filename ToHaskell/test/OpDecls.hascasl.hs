module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data A__s = A__s
          deriving (Show, Eq, Ord)
 
data A__t = A__t
          deriving (Show, Eq, Ord)
 
a___2_P_2 :: (A__s, A__s) -> A__s
a___2_P_2 = undefined
 
x1 :: A__s
x1 = undefined
 
x2 :: A__s
x2 = undefined
 
y :: A__s
y = a___2_P_2 (x2, x2)
