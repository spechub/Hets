module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data A_s = A_s
         deriving (Show, Eq, Ord)
 
data A_t = A_t
         deriving (Show, Eq, Ord)
 
_2_P_2 :: (A_s, A_s) -> A_s
_2_P_2 = undefined
 
x1 :: A_s
x1 = undefined
 
x2 :: A_s
x2 = undefined
 
y :: A_s
y = _2_P_2 (x2, x2)
