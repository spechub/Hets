{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{-

types:
AT :: (*, data)
A__s :: (*, type _ = B)
B :: (*, data)
C :: (*, data)

values:
a___P :: (AT, B) -> C
f :: C -> C
f_02 :: B -> B
s1 :: AT -> Int
s2 :: AT -> B
A :: (Int, B) -> AT
B :: B
C :: C
Int :: Int

scope:
Prelude.A |-> Prelude.A, con of AT
Prelude.AT |-> Prelude.AT, Type [A] []
Prelude.A__s |-> Prelude.A__s, Type [] []
Prelude.B |-> Prelude.B, Type [B] []
Prelude.B |-> Prelude.B, con of B
Prelude.C |-> Prelude.C, Type [C] []
Prelude.C |-> Prelude.C, con of C
Prelude.Int |-> Prelude.Int, con of Int
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
Int |-> Prelude.Int, con of Int
a___P |-> Prelude.a___P, Value
f |-> Prelude.f, Value
f_02 |-> Prelude.f_02, Value
s1 |-> Prelude.s1, Value
s2 |-> Prelude.s2, Value
-}
module Dummy where
data B = B
data C = C
type A__s = B
a___P :: (AT, B) -> C
a___P = error{-((AT, B) -> C)-} "a___P"
f_02 :: B -> B
f_02 = error{-(B -> B)-} "f_02"
f :: C -> C
f = error{-(C -> C)-} "f"
s1 :: AT -> Int
s2 :: AT -> B
s1 (A (x_11, x_12)) = x_11
s2 (A (x_11, x_12)) = x_12
data AT = A !(Int, B)
