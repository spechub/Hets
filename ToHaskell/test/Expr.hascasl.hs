module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
a :: A__bool
 
b_02 :: A__bool -> A__bool
 
b :: A__bool
 
notA :: A__bool
 
data A__bool = A__True
             | A__False
             deriving (Show, Eq, Ord)
a = A__True
notA
  = case a of
        A__True -> A__False
        A__False -> A__True
b = let x = A__True
        y = A__False
        z = x
      in A__True
b_02 = \ x -> x
