module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data Nat = Zero
         | Suc !Nat
         deriving (Show, Eq, Ord)
 
f :: Nat -> Nat
f = undefined
 
prec :: Nat -> Nat
prec = undefined
