module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
a___2_L_E_2 :: (Nat, Nat) -> Unit
 
elem :: (Nat, List_FNat_J) -> Unit
 
head :: List_FNat_J -> Nat
 
insert :: (Nat, List_FNat_J) -> List_FNat_J
 
insert_1sort :: List_FNat_J -> List_FNat_J
 
is_1ordered :: List_FNat_J -> Unit
 
permutation :: (List_FNat_J, List_FNat_J) -> Unit
permutation = undefined
 
prec :: Nat -> Nat
 
sorter :: List_FNat_J -> List_FNat_J
sorter = undefined
 
tail :: List_FNat_J -> List_FNat_J
insert_1sort (Cons (x, a__L)) = insert (x, insert_1sort a__L)
insert_1sort Nil = Nil
insert (x, (Cons (y, a__L)))
  = a___2when_2else_2
      (Cons (x, insert (y, a__L)), a___2_L_E_2 (x, y),
       Cons (y, insert (x, a__L)))
insert (x, Nil) = Cons (x, Nil)
is_1ordered (Cons (x, (Cons (y, a__L))))
  = a___2_S_B_2 (a___2_L_E_2 (x, y), is_1ordered (Cons (y, a__L)))
is_1ordered (Cons (x, Nil)) = true
is_1ordered Nil = true
elem (x, (Cons (y, l)))
  = a___2_B_S_2 (a___2_E_2 (x, y), elem (x, l))
elem (x, Nil) = false
 
data List_FNat_J = Nil
                 | Cons !(Nat, List_FNat_J)
                 deriving (Show, Eq, Ord)
tail (Cons (x_11_11, x_11_12)) = x_11_12
head (Cons (x_11_11, x_11_12)) = x_11_11
a___2_L_E_2 (x, y)
  = a___2when_2else_2 (true, a___2_E_2 (x, y), bottom)
a___2_L_E_2 ((Succ x), (Succ y)) = a___2_L_E_2 (x, y)
a___2_L_E_2 ((Succ x), A__0) = false
a___2_L_E_2 (A__0, x) = true
 
data Nat = A__0
         | Succ !Nat
         deriving (Show, Eq, Ord)
prec (Succ x_11_11) = x_11_11
