{-

types:
A__bool :: (*, data)

values:
a :: A__bool
b :: A__bool
b_02 :: A__bool -> A__bool
notA :: A__bool
False :: A__bool
True :: A__bool

scope:
Prelude.A__bool |-> Prelude.A__bool, Type [True,
					   False] []
Prelude.False |-> Prelude.False, con of A__bool
Prelude.True |-> Prelude.True, con of A__bool
Prelude.a |-> Prelude.a, Value
Prelude.b |-> Prelude.b, Value
Prelude.b_02 |-> Prelude.b_02, Value
Prelude.notA |-> Prelude.notA, Value
A__bool |-> Prelude.A__bool, Type [True, False] []
False |-> Prelude.False, con of A__bool
True |-> Prelude.True, con of A__bool
a |-> Prelude.a, Value
b |-> Prelude.b, Value
b_02 |-> Prelude.b_02, Value
notA |-> Prelude.notA, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord)
import MyLogic
a :: A__bool
b_02 :: A__bool -> A__bool
b :: A__bool
notA :: A__bool
data A__bool = True | False
a = True
notA
    =   case a of
	    True -> False
	    False -> True
b   =   let x = True
	     
	    y = False
	     
	    z = x
	in True
b_02 = \ x -> x
