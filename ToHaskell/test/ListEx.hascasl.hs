module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data List a = Nil
            | Cons !(a, List a)
            deriving (Show, Eq, Ord)
 
f :: List a -> List a
f = undefined
 
g :: List a -> List a
g = undefined
 
head :: List a -> a
head = undefined
 
tail :: List a -> List a
tail = undefined
