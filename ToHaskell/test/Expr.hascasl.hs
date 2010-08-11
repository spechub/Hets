{-

values:
a :: Bool
b :: Bool -> Bool
b_02 :: Bool
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
a :: Bool
b_02 :: Bool
b :: Bool -> Bool
notA :: Bool
a = True
notA
    =
        case a of
            True -> False
            False -> True
b_02
    =
        let x = True
            y = False
            z = x
            {-
            x :: Bool
            y :: Bool
            z :: Bool
            -}
        in True
b = \ x -> x
