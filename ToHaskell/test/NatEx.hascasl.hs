module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
f :: Nat -> Nat
 
prec :: Nat -> Nat
prec (Suc x_11_11) = x_11_11
 
data Nat = Zero
         | Suc !Nat
         deriving (Show, Eq, Ord)
f x = Suc x
