{-
instances:
(Eq B, (derived__Prelude_Eq_B, []))
(Ord B, (derived__Prelude_Ord_B, []))
(Show B, (derived__Prelude_Show_B, []))
(Eq C, (derived__Prelude_Eq_C, []))
(Ord C, (derived__Prelude_Ord_C, []))
(Show C, (derived__Prelude_Show_C, []))
(Eq AT, (derived__Prelude_Eq_AT, []))
(Ord AT, (derived__Prelude_Ord_AT, []))
(Show AT, (derived__Prelude_Show_AT, []))

types:
AT :: (*, data)
A__s :: (*, type _ = B)
B :: (*, data)
C :: (*, data)

values:
a___P :: (AT, B) -> C
derived__Prelude_Eq_AT :: Eq AT
derived__Prelude_Eq_B :: Eq B
derived__Prelude_Eq_C :: Eq C
derived__Prelude_Ord_AT :: Ord AT
derived__Prelude_Ord_B :: Ord B
derived__Prelude_Ord_C :: Ord C
derived__Prelude_Show_AT :: Show AT
derived__Prelude_Show_B :: Show B
derived__Prelude_Show_C :: Show C
f :: B -> B
f_02 :: C -> C
s1 :: AT -> Int
s2 :: AT -> B
A :: (Int, B) -> AT
B :: B
C :: C

scope:
Prelude.A |-> Prelude.A, con of AT
Prelude.AT |-> Prelude.AT, Type [A] []
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
import MyLogic
data B = B deriving (Show, Eq, Ord)
data C = C deriving (Show, Eq, Ord)
type A__s = B
a___P :: (AT, B) -> C
a___P = error{-((AT, B) -> C)-} "a___P"
f_02 :: C -> C
f_02 = error{-(C -> C)-} "f_02"
f :: B -> B
f = error{-(B -> B)-} "f"
s1 :: AT -> Int
s2 :: AT -> B
s1 (A (x_11_11, x_11_12)) = x_11_11
s2 (A (x_11_11, x_11_12)) = x_11_12
data AT = A !(Int, B) deriving (Show, Eq, Ord)
