{-

types:
Nat :: (*, data)

values:
f :: Nat -> Nat
prec :: Nat -> Nat
Suc :: Nat -> Nat
Zero :: Nat

scope:
Prelude.Nat |-> Prelude.Nat, Type [Suc, Zero] []
Prelude.Suc |-> Prelude.Suc, con of Nat
Prelude.Zero |-> Prelude.Zero, con of Nat
Prelude.f |-> Prelude.f, Value
Prelude.prec |-> Prelude.prec, Value
Nat |-> Prelude.Nat, Type [Suc, Zero] []
Suc |-> Prelude.Suc, con of Nat
Zero |-> Prelude.Zero, con of Nat
f |-> Prelude.f, Value
prec |-> Prelude.prec, Value
-}
module Dummy where
f :: Nat -> Nat
prec :: Nat -> Nat
prec (Suc x_11) = x_11
data Nat = Suc !Nat | Zero
f x = Suc x
