{-

types:
List :: (*->*, data)

values:
foldl ::
    forall a b . a -> (a -> b -> a) -> (List b) -> a
A__cons :: forall a . a -> (List a) -> List a
A__nil :: forall a . List a

scope:
Prelude.A__cons |-> Prelude.A__cons, con of List
Prelude.A__nil |-> Prelude.A__nil, con of List
Prelude.List |-> Prelude.List, Type [A__nil,
				     A__cons] []
Prelude.foldl |-> Prelude.foldl, Value
A__cons |-> Prelude.A__cons, con of List
A__nil |-> Prelude.A__nil, con of List
List |-> Prelude.List, Type [A__nil, A__cons] []
foldl |-> Prelude.foldl, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord)
import MyLogic
foldl :: b -> (b -> a -> b) -> (List a) -> b
data List a = A__nil | A__cons !a !(List a)
foldl z f A__nil{-a-} = z
foldl z f (A__cons{-a-} x l)
    = foldl{-b a-} (f z x) f l
