{-
instances:
Eq A__a
Ord A__a
Show A__a
Eq A__b
Ord A__b
Show A__b
Eq Pair
Ord Pair
Show Pair

types:
A__a :: (*, data)
A__b :: (*, data)
Pair :: (*, data)

values:
derived__Prelude_Eq_A__a :: Eq A__a
derived__Prelude_Eq_A__b :: Eq A__b
derived__Prelude_Eq_Pair :: Eq Pair
derived__Prelude_Ord_A__a :: Ord A__a
derived__Prelude_Ord_A__b :: Ord A__b
derived__Prelude_Ord_Pair :: Ord Pair
derived__Prelude_Show_A__a :: Show A__a
derived__Prelude_Show_A__b :: Show A__b
derived__Prelude_Show_Pair :: Show Pair
f :: (A__a, A__b) -> Pair
g :: Pair -> A__a
A__a :: A__a
A__b :: A__b
Pair :: (A__a, A__b) -> Pair

scope:
Prelude.A__a |-> Prelude.A__a, Type [A__a] []
Prelude.A__a |-> Prelude.A__a, con of A__a
Prelude.A__b |-> Prelude.A__b, Type [A__b] []
Prelude.A__b |-> Prelude.A__b, con of A__b
Prelude.Pair |-> Prelude.Pair, Type [Pair] []
Prelude.Pair |-> Prelude.Pair, con of Pair
Prelude.f |-> Prelude.f, Value
Prelude.g |-> Prelude.g, Value
A__a |-> Prelude.A__a, Type [A__a] []
A__a |-> Prelude.A__a, con of A__a
A__b |-> Prelude.A__b, Type [A__b] []
A__b |-> Prelude.A__b, con of A__b
Pair |-> Prelude.Pair, Type [Pair] []
Pair |-> Prelude.Pair, con of Pair
f |-> Prelude.f, Value
g |-> Prelude.g, Value
-}
module Dummy where
import MyLogic
data A__a = A__a deriving (Show, Eq, Ord)
data A__b = A__b deriving (Show, Eq, Ord)
f :: (A__a, A__b) -> Pair
g :: Pair -> A__a
data Pair
    = Pair !(A__a, A__b) deriving (Show, Eq, Ord)
f (a, b) = Pair (a, b)
g (Pair (a, b)) = a
