module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data B = B
       deriving (Show, Eq, Ord)
 
data C = C
       deriving (Show, Eq, Ord)
 
data A__Int = A__Int
            deriving (Show, Eq, Ord)
 
type A__s = B
 
a___P :: (AT, B) -> C
a___P = undefined
 
f_02 :: C -> C
f_02 = undefined
 
f :: B -> B
f = undefined
 
s1 :: AT -> A__Int
 
s2 :: AT -> B
s1 (A (x_11_11, x_11_12)) = x_11_11
s2 (A (x_11_11, x_11_12)) = x_11_12
 
data AT = A !(A__Int, B)
        deriving (Show, Eq, Ord)
