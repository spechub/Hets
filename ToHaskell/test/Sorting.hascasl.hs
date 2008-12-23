{-

types:
List_FNat_J :: (*, data)
Nat :: (*, data)

values:
a___2_L_E_2 :: (Nat, Nat) -> Bool
insert :: (Nat, List_FNat_J) -> List_FNat_J
insert_1sort :: List_FNat_J -> List_FNat_J
is_1ordered :: List_FNat_J -> Bool
permutation :: (List_FNat_J, List_FNat_J) -> Bool
prec :: Nat -> Nat
sorter :: List_FNat_J -> List_FNat_J
A__0 :: Nat
Cons :: (Nat, List_FNat_J) -> List_FNat_J
Nil :: List_FNat_J
Succ :: Nat -> Nat

scope:
Prelude.A__0 |-> Prelude.A__0, con of Nat
Prelude.Cons |-> Prelude.Cons, con of List_FNat_J
Prelude.List_FNat_J |-> Prelude.List_FNat_J, Type [Cons,
                                                   Nil] []
Prelude.Nat |-> Prelude.Nat, Type [A__0, Succ] []
Prelude.Nil |-> Prelude.Nil, con of List_FNat_J
Prelude.Succ |-> Prelude.Succ, con of Nat
Prelude.a___2_L_E_2 |-> Prelude.a___2_L_E_2, Value
Prelude.insert |-> Prelude.insert, Value
Prelude.insert_1sort |-> Prelude.insert_1sort, Value
Prelude.is_1ordered |-> Prelude.is_1ordered, Value
Prelude.permutation |-> Prelude.permutation, Value
Prelude.prec |-> Prelude.prec, Value
Prelude.sorter |-> Prelude.sorter, Value
A__0 |-> Prelude.A__0, con of Nat
Cons |-> Prelude.Cons, con of List_FNat_J
List_FNat_J |-> Prelude.List_FNat_J, Type [Cons,
                                           Nil] []
Nat |-> Prelude.Nat, Type [A__0, Succ] []
Nil |-> Prelude.Nil, con of List_FNat_J
Succ |-> Prelude.Succ, con of Nat
a___2_L_E_2 |-> Prelude.a___2_L_E_2, Value
insert |-> Prelude.insert, Value
insert_1sort |-> Prelude.insert_1sort, Value
is_1ordered |-> Prelude.is_1ordered, Value
permutation |-> Prelude.permutation, Value
prec |-> Prelude.prec, Value
sorter |-> Prelude.sorter, Value
-}
module Dummy where
a___2_L_E_2 :: (Nat, Nat) -> Bool
insert :: (Nat, List_FNat_J) -> List_FNat_J
insert_1sort :: List_FNat_J -> List_FNat_J
is_1ordered :: List_FNat_J -> Bool
permutation :: (List_FNat_J, List_FNat_J) -> Bool
permutation
    =
        error{-((List_FNat_J, List_FNat_J) -> Bool)-}
            "permutation"
prec :: Nat -> Nat
sorter :: List_FNat_J -> List_FNat_J
sorter
    = error{-(List_FNat_J -> List_FNat_J)-} "sorter"
prec (Succ x_11_11) = x_11_11
data Nat = A__0 | Succ !Nat
a___2_L_E_2 (A__0, x) = True
a___2_L_E_2 ((Succ x), A__0) = False
a___2_L_E_2 ((Succ x), (Succ y)) = a___2_L_E_2 (x, y)
a___2_L_E_2 (x, y)
    =
        (\ (a, b, c) -> if b then a else c)
            (True,
             error{-(((,) Nat Nat) -> Bool)-}
                 "equality at Sorting.hascasl:14,7"
                 (x, y),
             error{-Bool-} "bottom at __unknown__:0,0")
data List_FNat_J = Cons !(Nat, List_FNat_J) | Nil
is_1ordered Nil = True
is_1ordered (Cons (x, Nil)) = True
is_1ordered (Cons (x, (Cons (y, a__L))))
    =
        uncurry{-Bool Bool Bool-} (&&)
            (a___2_L_E_2 (x, y), is_1ordered (Cons (y, a__L)))
insert (x, Nil) = Cons (x, Nil)
insert (x, (Cons (y, a__L)))
    =
        (\ (a, b, c) -> if b then a else c)
            (Cons (x, insert (y, a__L)), a___2_L_E_2 (x, y),
             Cons (y, insert (x, a__L)))
insert_1sort Nil = Nil
insert_1sort (Cons (x, a__L))
    = insert (x, insert_1sort a__L)
