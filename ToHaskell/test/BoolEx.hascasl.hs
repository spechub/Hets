module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
eq :: (A_Bool, A_Bool) -> A_Bool
 
le :: (A_Bool, A_Bool) -> A_Bool
 
ne :: (A_Bool, A_Bool) -> A_Bool
 
neg :: A_Bool -> A_Bool
 
vee :: (A_Bool, A_Bool) -> A_Bool
 
wedge :: (A_Bool, A_Bool) -> A_Bool
 
data A_Bool = A_True
            | A_False
            deriving (Show, Eq, Ord)
neg x
  = case x of
        A_False -> A_True
        A_True -> A_False
wedge (x, y)
  = case (x, y) of
        (A_False, A_False) -> A_False
        (A_True, A_False) -> A_False
        (A_False, A_True) -> A_False
        (A_True, A_True) -> A_True
vee (x, y) = neg (wedge (neg x, neg y))
le (x, y) = vee (neg x, y)
eq (x, y) = wedge (le (x, y), le (y, x))
ne (x, y) = wedge (vee (x, y), neg (wedge (x, y)))
