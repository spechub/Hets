module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
eq :: (A__Bool, A__Bool) -> A__Bool
 
le :: (A__Bool, A__Bool) -> A__Bool
 
ne :: (A__Bool, A__Bool) -> A__Bool
 
neg :: A__Bool -> A__Bool
 
vee :: (A__Bool, A__Bool) -> A__Bool
 
wedge :: (A__Bool, A__Bool) -> A__Bool
ne (x, y) = wedge (vee (x, y), neg (wedge (x, y)))
eq (x, y) = wedge (le (x, y), le (y, x))
le (x, y) = vee (neg x, y)
vee (x, y) = neg (wedge (neg x, neg y))
wedge (x, y)
  = case (x, y) of
        (A__False, A__False) -> A__False
        (A__True, A__False) -> A__False
        (A__False, A__True) -> A__False
        (A__True, A__True) -> A__True
neg x
  = case x of
        A__False -> A__True
        A__True -> A__False
 
data A__Bool = A__True
             | A__False
             deriving (Show, Eq, Ord)
