-- Kind.hs
-- no output - 

module Foo where

data B b = Barfoo (b Int)
data C c = Foobar (B c) | Foobar2 (c Int)

-- some non-reular types:

newtype Copy a = C a -- deriving Show

instance Show (Copy a) where
  show x = "haha"

data Wonky f = W | M (f (Wonky f)) 


data Sport f
  = Sport
  | Association (f Bool)


