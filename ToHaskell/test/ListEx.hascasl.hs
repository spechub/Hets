{-
instances:
Eq (List a)
Ord (List a)
Show (List a)

types:
List :: (*->*, data)

values:
derived__Prelude_Eq_List ::
    forall a . (Eq a) -> Eq (List a)
derived__Prelude_Ord_List ::
    forall a . (Ord a) -> Ord (List a)
derived__Prelude_Show_List ::
    forall a . (Show a) -> Show (List a)
myhead :: forall a . (List a) -> a
Cons :: forall a . (a, List a) -> List a
Nil :: forall a . List a

scope:
Prelude.Cons |-> Prelude.Cons, con of List
Prelude.List |-> Prelude.List, Type [Nil, Cons] []
Prelude.Nil |-> Prelude.Nil, con of List
Prelude.myhead |-> Prelude.myhead, Value
Cons |-> Prelude.Cons, con of List
List |-> Prelude.List, Type [Nil, Cons] []
Nil |-> Prelude.Nil, con of List
myhead |-> Prelude.myhead, Value
-}
module Dummy where
import MyLogic
myhead :: (List a) -> a
myhead (Cons{-a-} (x_11_11, x_11_12)) = x_11_11
data List a
    = Nil | Cons !(a, List a) deriving (Show, Eq, Ord)
