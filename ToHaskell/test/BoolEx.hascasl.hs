module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data A_Bool = A_True
            | A_False
            deriving (Show, Eq, Ord)
 
eq :: (A_Bool, A_Bool) -> A_Bool
eq = undefined
 
le :: (A_Bool, A_Bool) -> A_Bool
le = undefined
 
ne :: (A_Bool, A_Bool) -> A_Bool
ne = undefined
 
neg :: A_Bool -> A_Bool
neg = undefined
 
vee :: (A_Bool, A_Bool) -> A_Bool
vee = undefined
 
wedge :: (A_Bool, A_Bool) -> A_Bool
wedge = undefined
