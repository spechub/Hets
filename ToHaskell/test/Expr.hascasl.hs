module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
a :: A_bool
 
b0 :: A_bool -> A_bool
b0 = undefined
 
b :: A_bool
 
notA :: A_bool
 
data A_bool = A_True
            | A_False
            deriving (Show, Eq, Ord)
a = A_True
notA
  = case a of
        A_True -> A_False
        A_False -> A_True
b = let x = A_True
        y = A_False
        z = x
      in A_True
b = \ x -> x
