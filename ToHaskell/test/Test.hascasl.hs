{-

types:
AT :: (*, data)
A__Int :: (*, data)
A__s :: (*, type _ = B)
B :: (*, data)
C :: (*, data)

values:
a___P :: (AT, B) -> C
f :: B -> B
f_02 :: C -> C
s1 :: AT -> A__Int
s2 :: AT -> B
A :: (A__Int, B) -> AT
A__Int :: A__Int
B :: B
C :: C

scope:
Prelude.A |-> Prelude.A, con of AT
Prelude.AT |-> Prelude.AT, Type [A] []
Prelude.A__Int |-> Prelude.A__Int, Type [A__Int] []
Prelude.A__Int |-> Prelude.A__Int, con of A__Int
Prelude.A__s |-> Prelude.A__s, Type [] []
Prelude.B |-> Prelude.B, Type [B] []
Prelude.B |-> Prelude.B, con of B
Prelude.C |-> Prelude.C, Type [C] []
Prelude.C |-> Prelude.C, con of C
Prelude.a___P |-> Prelude.a___P, Value
Prelude.f |-> Prelude.f, Value
Prelude.f_02 |-> Prelude.f_02, Value
Prelude.s1 |-> Prelude.s1, Value
Prelude.s2 |-> Prelude.s2, Value
A |-> Prelude.A, con of AT
AT |-> Prelude.AT, Type [A] []
A__Int |-> Prelude.A__Int, Type [A__Int] []
A__Int |-> Prelude.A__Int, con of A__Int
A__s |-> Prelude.A__s, Type [] []
B |-> Prelude.B, Type [B] []
B |-> Prelude.B, con of B
C |-> Prelude.C, Type [C] []
C |-> Prelude.C, con of C
a___P |-> Prelude.a___P, Value
f |-> Prelude.f, Value
f_02 |-> Prelude.f_02, Value
s1 |-> Prelude.s1, Value
s2 |-> Prelude.s2, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord, Bool)
import MyLogic
data B = B
data C = C
data A__Int = A__Int
type A__s = B
a___P :: (AT, B) -> C
a___P = error "a___P"
f_02 :: C -> C
f_02 = error "f_02"
f :: B -> B
f = error "f"
s1 :: AT -> A__Int
s2 :: AT -> B
s1 (A (x_11_11, x_11_12)) = x_11_11
s2 (A (x_11_11, x_11_12)) = x_11_12
data AT = A !(A__Int, B)
