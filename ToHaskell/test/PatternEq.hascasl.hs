{-
instances:
(Eq A__s, (derived__Prelude_Eq_A__s, []))
(Ord A__s, (derived__Prelude_Ord_A__s, []))
(Show A__s, (derived__Prelude_Show_A__s, []))
(Eq A__t, (derived__Prelude_Eq_A__t, []))
(Ord A__t, (derived__Prelude_Ord_A__t, []))
(Show A__t, (derived__Prelude_Show_A__t, []))

types:
A__s :: (*, data)
A__t :: (*, data)

values:
a :: A__s
b :: A__s
c :: A__t
derived__Prelude_Eq_A__s :: Eq A__s
derived__Prelude_Eq_A__t :: Eq A__t
derived__Prelude_Ord_A__s :: Ord A__s
derived__Prelude_Ord_A__t :: Ord A__t
derived__Prelude_Show_A__s :: Show A__s
derived__Prelude_Show_A__t :: Show A__t
x :: A__s
y :: A__t
A__s :: A__s
A__t :: A__t

scope:
Prelude.A__s |-> Prelude.A__s, Type [A__s] []
Prelude.A__s |-> Prelude.A__s, con of A__s
Prelude.A__t |-> Prelude.A__t, Type [A__t] []
Prelude.A__t |-> Prelude.A__t, con of A__t
Prelude.a |-> Prelude.a, Value
Prelude.b |-> Prelude.b, Value
Prelude.c |-> Prelude.c, Value
Prelude.x |-> Prelude.x, Value
Prelude.y |-> Prelude.y, Value
A__s |-> Prelude.A__s, Type [A__s] []
A__s |-> Prelude.A__s, con of A__s
A__t |-> Prelude.A__t, Type [A__t] []
A__t |-> Prelude.A__t, con of A__t
a |-> Prelude.a, Value
b |-> Prelude.b, Value
c |-> Prelude.c, Value
x |-> Prelude.x, Value
y |-> Prelude.y, Value
-}
module Dummy where
import MyLogic
data A__s = A__s deriving (Show, Eq, Ord)
data A__t = A__t deriving (Show, Eq, Ord)
a :: A__s
a = error{-A__s-} "a"
b :: A__s
c :: A__t
x :: A__s
x = error{-A__s-} "x"
y :: A__t
y = error{-A__t-} "y"
b = a
c = snd{-A__s A__t-} (x, y)
