module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data AT = A !(A_Int, B)
        deriving (Show, Eq, Ord)
 
data B = B
       deriving (Show, Eq, Ord)
 
data C = C
       deriving (Show, Eq, Ord)
 
data A_Int = A_Int
           deriving (Show, Eq, Ord)
 
type A_s = B
 
_P :: (AT, B) -> C
_P = undefined
 
f0 :: C -> C
f0 = undefined
 
f :: B -> B
f = undefined
 
s1 :: AT -> A_Int
s1 = undefined
 
s2 :: AT -> B
s2 = undefined
