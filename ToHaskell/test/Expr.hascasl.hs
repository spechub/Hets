{-

values:
a :: Bool
b :: Bool
b_02 :: Bool -> Bool
notA :: Bool

scope:
Prelude.a |-> Prelude.a, Value
Prelude.b |-> Prelude.b, Value
Prelude.b_02 |-> Prelude.b_02, Value
Prelude.notA |-> Prelude.notA, Value
a |-> Prelude.a, Value
b |-> Prelude.b, Value
b_02 |-> Prelude.b_02, Value
notA |-> Prelude.notA, Value
-}
module Dummy where
import MyLogic
a :: Bool
b_02 :: Bool -> Bool
b :: Bool
notA :: Bool
a = True
notA
    =   case a of
            True -> False
            False -> True
b   =   let x = True
            y = False
            z = x
            {-
            x :: Bool
            y :: Bool
            z :: Bool
            -}
        in True
b_02 = \ x -> x
