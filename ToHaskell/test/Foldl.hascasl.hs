{-
instances:
(Eq (List a), (derived__Prelude_Eq_List, [Eq a]))
(Ord (List a), (derived__Prelude_Ord_List, [Ord a]))
(Show (List a), (derived__Prelude_Show_List, [Show a]))

types:
List :: (*->*, data)

values:
derived__Prelude_Eq_List ::
    forall a . (Eq a) -> Eq (List a)
derived__Prelude_Ord_List ::
    forall a . (Ord a) -> Ord (List a)
derived__Prelude_Show_List ::
    forall a . (Show a) -> Show (List a)
A__cons :: forall a . a -> (List a) -> List a
A__nil :: forall a . List a

scope:
Prelude.A__cons |-> Prelude.A__cons, con of List
Prelude.A__nil |-> Prelude.A__nil, con of List
Prelude.List |-> Prelude.List, Type [A__nil,
				     A__cons] []
A__cons |-> Prelude.A__cons, con of List
A__nil |-> Prelude.A__nil, con of List
List |-> Prelude.List, Type [A__nil, A__cons] []
-}
module Dummy where
import MyLogic
data List a
    = A__nil | A__cons !a !(List a)
    deriving (Show, Eq, Ord)
