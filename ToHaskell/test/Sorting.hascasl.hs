{-

types:
List_FNat_J :: (*, data)
Nat :: (*, data)

values:
a___2_L_E_2 :: (Nat, Nat) -> Unit
elem :: (Nat, List_FNat_J) -> Unit
head :: List_FNat_J -> Nat
insert :: (Nat, List_FNat_J) -> List_FNat_J
insert_1sort :: List_FNat_J -> List_FNat_J
is_1ordered :: List_FNat_J -> Unit
permutation :: (List_FNat_J, List_FNat_J) -> Unit
prec :: Nat -> Nat
sorter :: List_FNat_J -> List_FNat_J
tail :: List_FNat_J -> List_FNat_J
A__0 :: Nat
Cons :: (Nat, List_FNat_J) -> List_FNat_J
Nil :: List_FNat_J
Succ :: Nat -> Nat

scope:
Prelude.A__0 |-> Prelude.A__0, con of Nat
Prelude.Cons |-> Prelude.Cons, con of List_FNat_J
Prelude.List_FNat_J |-> Prelude.List_FNat_J, Type [Nil,
						   Cons] []
Prelude.Nat |-> Prelude.Nat, Type [A__0, Succ] []
Prelude.Nil |-> Prelude.Nil, con of List_FNat_J
Prelude.Succ |-> Prelude.Succ, con of Nat
Prelude.a___2_L_E_2 |-> Prelude.a___2_L_E_2, Value
Prelude.elem |-> Prelude.elem, Value
Prelude.head |-> Prelude.head, Value
Prelude.insert |-> Prelude.insert, Value
Prelude.insert_1sort |-> Prelude.insert_1sort, Value
Prelude.is_1ordered |-> Prelude.is_1ordered, Value
Prelude.permutation |-> Prelude.permutation, Value
Prelude.prec |-> Prelude.prec, Value
Prelude.sorter |-> Prelude.sorter, Value
Prelude.tail |-> Prelude.tail, Value
A__0 |-> Prelude.A__0, con of Nat
Cons |-> Prelude.Cons, con of List_FNat_J
List_FNat_J |-> Prelude.List_FNat_J, Type [Nil,
					   Cons] []
Nat |-> Prelude.Nat, Type [A__0, Succ] []
Nil |-> Prelude.Nil, con of List_FNat_J
Succ |-> Prelude.Succ, con of Nat
a___2_L_E_2 |-> Prelude.a___2_L_E_2, Value
elem |-> Prelude.elem, Value
head |-> Prelude.head, Value
insert |-> Prelude.insert, Value
insert_1sort |-> Prelude.insert_1sort, Value
is_1ordered |-> Prelude.is_1ordered, Value
permutation |-> Prelude.permutation, Value
prec |-> Prelude.prec, Value
sorter |-> Prelude.sorter, Value
tail |-> Prelude.tail, Value
-}
module Dummy where
import Prelude (error, Show, Eq, Ord)
import MyLogic
a___2_L_E_2 :: (Nat, Nat) -> Unit
elem :: (Nat, List_FNat_J) -> Unit
head :: List_FNat_J -> Nat
insert :: (Nat, List_FNat_J) -> List_FNat_J
insert_1sort :: List_FNat_J -> List_FNat_J
is_1ordered :: List_FNat_J -> Unit
permutation :: (List_FNat_J, List_FNat_J) -> Unit
permutation
    =   error{-((List_FNat_J, List_FNat_J) -> Unit)-}
	    "permutation"
prec :: Nat -> Nat
sorter :: List_FNat_J -> List_FNat_J
sorter
    = error{-(List_FNat_J -> List_FNat_J)-} "sorter"
tail :: List_FNat_J -> List_FNat_J
prec (Succ x_11_11) = x_11_11
data Nat = A__0 | Succ !Nat
a___2_L_E_2 (A__0, x) = true
a___2_L_E_2 ((Succ x), A__0) = false
a___2_L_E_2 ((Succ x), (Succ y)) = a___2_L_E_2 (x, y)
a___2_L_E_2 (x, y)
    =   a___2when_2else_2{-Unit-}
	    (true, a___2_E_2{-Nat-} (x, y), bottom{-Unit-})
head (Cons (x_11_11, x_11_12)) = x_11_11
tail (Cons (x_11_11, x_11_12)) = x_11_12
data List_FNat_J = Nil | Cons !(Nat, List_FNat_J)
elem (x, Nil) = false
elem (x, (Cons (y, l)))
    = a___2_B_S_2 (a___2_E_2{-Nat-} (x, y), elem (x, l))
is_1ordered Nil = true
is_1ordered (Cons (x, Nil)) = true
is_1ordered (Cons (x, (Cons (y, a__L))))
    =   a___2_S_B_2
	    (a___2_L_E_2 (x, y), is_1ordered (Cons (y, a__L)))
insert (x, Nil) = Cons (x, Nil)
insert (x, (Cons (y, a__L)))
    =   a___2when_2else_2{-List_FNat_J-}
	    (Cons (x, insert (y, a__L)), a___2_L_E_2 (x, y),
	     Cons (y, insert (x, a__L)))
insert_1sort Nil = Nil
insert_1sort (Cons (x, a__L))
    = insert (x, insert_1sort a__L)
