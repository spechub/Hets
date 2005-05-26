{-
instances:
Eq Nat
Ord Nat
Show Nat

types:
Nat :: (*, data)

values:
derived__Prelude_Eq_Nat :: Eq Nat
derived__Prelude_Ord_Nat :: Ord Nat
derived__Prelude_Show_Nat :: Show Nat
f :: Nat -> Nat
prec :: Nat -> Nat
Suc :: Nat -> Nat
Zero :: Nat

scope:
Prelude.Nat |-> Prelude.Nat, Type [Zero, Suc] []
Prelude.Suc |-> Prelude.Suc, con of Nat
Prelude.Zero |-> Prelude.Zero, con of Nat
Prelude.f |-> Prelude.f, Value
Prelude.prec |-> Prelude.prec, Value
Nat |-> Prelude.Nat, Type [Zero, Suc] []
Suc |-> Prelude.Suc, con of Nat
Zero |-> Prelude.Zero, con of Nat
f |-> Prelude.f, Value
prec |-> Prelude.prec, Value
-}
module Dummy where
import MyLogic
f :: Nat -> Nat
prec :: Nat -> Nat
prec (Suc x_11_11) = x_11_11
data Nat = Zero | Suc !Nat deriving (Show, Eq, Ord)
f x = Suc x
