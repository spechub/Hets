{-

types:
A__a :: (*, data)
A__b :: (*, data)
Pair :: (*, data)

values:
a__fst :: Pair -> A__a
a__snd :: Pair -> A__b
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
Prelude.a__fst |-> Prelude.a__fst, Value
Prelude.a__snd |-> Prelude.a__snd, Value
Prelude.f |-> Prelude.f, Value
Prelude.g |-> Prelude.g, Value
A__a |-> Prelude.A__a, Type [A__a] []
A__a |-> Prelude.A__a, con of A__a
A__b |-> Prelude.A__b, Type [A__b] []
A__b |-> Prelude.A__b, con of A__b
Pair |-> Prelude.Pair, Type [Pair] []
Pair |-> Prelude.Pair, con of Pair
a__fst |-> Prelude.a__fst, Value
a__snd |-> Prelude.a__snd, Value
f |-> Prelude.f, Value
g |-> Prelude.g, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord, Bool)
import MyLogic
data A__a = A__a
data A__b = A__b
f :: (A__a, A__b) -> Pair
a__fst :: Pair -> A__a
g :: Pair -> A__a
a__snd :: Pair -> A__b
a__fst (Pair (x_11_11, x_11_12)) = x_11_11
a__snd (Pair (x_11_11, x_11_12)) = x_11_12
data Pair = Pair !(A__a, A__b)
f (a, b) = Pair (a, b)
g (Pair (a, b)) = a
