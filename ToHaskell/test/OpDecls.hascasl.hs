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
a___2_P_2 :: (A__s, A__s) -> A__s
derived__Prelude_Eq_A__s :: Eq A__s
derived__Prelude_Eq_A__t :: Eq A__t
derived__Prelude_Ord_A__s :: Ord A__s
derived__Prelude_Ord_A__t :: Ord A__t
derived__Prelude_Show_A__s :: Show A__s
derived__Prelude_Show_A__t :: Show A__t
x1 :: A__s
x2 :: A__s
y :: A__s
A__s :: A__s
A__t :: A__t

scope:
Prelude.A__s |-> Prelude.A__s, Type [A__s] []
Prelude.A__s |-> Prelude.A__s, con of A__s
Prelude.A__t |-> Prelude.A__t, Type [A__t] []
Prelude.A__t |-> Prelude.A__t, con of A__t
Prelude.a___2_P_2 |-> Prelude.a___2_P_2, Value
Prelude.x1 |-> Prelude.x1, Value
Prelude.x2 |-> Prelude.x2, Value
Prelude.y |-> Prelude.y, Value
A__s |-> Prelude.A__s, Type [A__s] []
A__s |-> Prelude.A__s, con of A__s
A__t |-> Prelude.A__t, Type [A__t] []
A__t |-> Prelude.A__t, con of A__t
a___2_P_2 |-> Prelude.a___2_P_2, Value
x1 |-> Prelude.x1, Value
x2 |-> Prelude.x2, Value
y |-> Prelude.y, Value
-}
module Dummy where
import MyLogic
data A__s = A__s deriving (Show, Eq, Ord)
data A__t = A__t deriving (Show, Eq, Ord)
a___2_P_2 :: (A__s, A__s) -> A__s
a___2_P_2
    = error{-((A__s, A__s) -> A__s)-} "a___2_P_2"
x1 :: A__s
x1 = error{-A__s-} "x1"
x2 :: A__s
x2 = error{-A__s-} "x2"
y :: A__s
y = a___2_P_2 (x2, x2)
