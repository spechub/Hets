{-

types:
A__s :: (*, data)
A__t :: (*, data)

values:
a :: A__s
a__snd :: (A__s, A__t) -> A__t
b :: A__s
c :: A__t
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
Prelude.a__snd |-> Prelude.a__snd, Value
Prelude.b |-> Prelude.b, Value
Prelude.c |-> Prelude.c, Value
Prelude.x |-> Prelude.x, Value
Prelude.y |-> Prelude.y, Value
A__s |-> Prelude.A__s, Type [A__s] []
A__s |-> Prelude.A__s, con of A__s
A__t |-> Prelude.A__t, Type [A__t] []
A__t |-> Prelude.A__t, con of A__t
a |-> Prelude.a, Value
a__snd |-> Prelude.a__snd, Value
b |-> Prelude.b, Value
c |-> Prelude.c, Value
x |-> Prelude.x, Value
y |-> Prelude.y, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord)
import MyLogic
data A__s = A__s
data A__t = A__t
a :: A__s
a = error{-A__s-} "a"
b :: A__s
c :: A__t
a__snd :: (A__s, A__t) -> A__t
x :: A__s
x = error{-A__s-} "x"
y :: A__t
y = error{-A__t-} "y"
a__snd (x, y) = y
b = a
c = a__snd (x, y)
