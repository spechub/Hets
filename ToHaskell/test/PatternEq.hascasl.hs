module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data A__s = A__s
          deriving (Show, Eq, Ord)
 
data A__t = A__t
          deriving (Show, Eq, Ord)
 
a :: A__s
a = undefined
 
b :: A__s
 
c :: A__t
 
a__snd :: (A__s, A__t) -> A__t
 
x :: A__s
x = undefined
 
y :: A__t
y = undefined
a__snd (x, y) = y
b = a
c = a__snd (x, y)
