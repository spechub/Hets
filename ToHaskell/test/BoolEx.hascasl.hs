{-

types:
Bool :: (*, data)

values:
eq :: (Bool, Bool) -> Bool
le :: (Bool, Bool) -> Bool
ne :: (Bool, Bool) -> Bool
neg :: Bool -> Bool
vee :: (Bool, Bool) -> Bool
wedge :: (Bool, Bool) -> Bool
False :: Bool
True :: Bool

scope:
Prelude.Bool |-> Prelude.Bool, Type [True, False] []
Prelude.False |-> Prelude.False, con of Bool
Prelude.True |-> Prelude.True, con of Bool
Prelude.eq |-> Prelude.eq, Value
Prelude.le |-> Prelude.le, Value
Prelude.ne |-> Prelude.ne, Value
Prelude.neg |-> Prelude.neg, Value
Prelude.vee |-> Prelude.vee, Value
Prelude.wedge |-> Prelude.wedge, Value
Bool |-> Prelude.Bool, Type [True, False] []
False |-> Prelude.False, con of Bool
True |-> Prelude.True, con of Bool
eq |-> Prelude.eq, Value
le |-> Prelude.le, Value
ne |-> Prelude.ne, Value
neg |-> Prelude.neg, Value
vee |-> Prelude.vee, Value
wedge |-> Prelude.wedge, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord, Bool)
import MyLogic
eq :: (Bool, Bool) -> Bool
le :: (Bool, Bool) -> Bool
ne :: (Bool, Bool) -> Bool
neg :: Bool -> Bool
vee :: (Bool, Bool) -> Bool
wedge :: (Bool, Bool) -> Bool
data Bool = True | False
neg x
    =   case x of
	    False -> True
	    True -> False
wedge (x, y)
    =   case (x, y) of
	    (False, False) -> False
	    (True, False) -> False
	    (False, True) -> False
	    (True, True) -> True
vee (x, y) = neg (wedge (neg x, neg y))
le (x, y) = vee (neg x, y)
eq (x, y) = wedge (le (x, y), le (y, x))
ne (x, y) = wedge (vee (x, y), neg (wedge (x, y)))
