module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
_2_L_E_2 :: (Nat, Nat) -> Bool
 
elem :: (Nat, List_FNat_J) -> Bool
 
head :: List_FNat_J -> Nat
 
insert :: (Nat, List_FNat_J) -> List_FNat_J
 
insert_1sort :: List_FNat_J -> List_FNat_J
 
is_1ordered :: List_FNat_J -> Bool
 
permutation :: (List_FNat_J, List_FNat_J) -> Bool
permutation = undefined
 
prec :: Nat -> Nat
 
sorter :: List_FNat_J -> List_FNat_J
sorter = undefined
 
tail :: List_FNat_J -> List_FNat_J
prec (Succ x_11_11) = x_11_11
 
data Nat = A_0
         | Succ !Nat
         deriving (Show, Eq, Ord)
_2_L_E_2 (A_0, x) = true
_2_L_E_2 ((Succ x), A_0) = false
_2_L_E_2 ((Succ x), (Succ y)) = _2_L_E_2 (x, y)
_2_E_2 (x, y)
  = _2when_2else_2
      (true, _2_S_B_2 (_2_L_E_2 (x, y), _2_L_E_2 (y, x)), _2_E_2 (x, y))
_2_L_E_2 (x, y)
  = _2when_2else_2 (true, _2_E_2 (x, y), _2_L_E_2 (x, y))
head (Cons (x_11_11, x_11_12)) = x_11_11
tail (Cons (x_11_11, x_11_12)) = x_11_12
 
data List_FNat_J = Nil
                 | Cons !(Nat, List_FNat_J)
                 deriving (Show, Eq, Ord)
elem (x, Nil) = false
elem (x, (Cons (y, l))) = _2_B_S_2 (_2_E_2 (x, y), elem (x, l))
is_1ordered Nil = true
is_1ordered (Cons (x, Nil)) = true
is_1ordered (Cons (x, (Cons (y, a_L))))
  = _2_S_B_2 (_2_L_E_2 (x, y), is_1ordered (Cons (y, a_L)))
insert (x, Nil) = Cons (x, Nil)
insert (x, (Cons (y, a_L)))
  = _2when_2else_2
      (Cons (x, insert (y, a_L)), _2_L_E_2 (x, y),
       Cons (y, insert (x, a_L)))
insert_1sort Nil = Nil
insert_1sort (Cons (x, a_L)) = insert (x, insert_1sort a_L)
