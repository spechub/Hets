module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
f :: Nat -> Nat
 
prec :: Nat -> Nat
f x = Suc x
 
data Nat = Zero
         | Suc !Nat
         deriving (Show, Eq, Ord)
prec (Suc x_11_11) = x_11_11
