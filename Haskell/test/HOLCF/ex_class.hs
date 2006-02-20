module SimpleClass where

data Color a = Red a | Blue a

data MyList a  = MyNil | MyCons a (MyList a)

data MPList a b = MPNil | MPCons a b (MPList a b)

myEqual        :: Eq a => a -> a -> Bool
myEqual x y    =   if x == y then True else False

instance Eq a => Eq (Color a)

instance Eq a => Eq (MyList a)

class Joker a where
 methodOne :: a -> a -> Bool
 methodTwo :: a -> Bool -> Color a

instance (Joker a, Eq a) => Joker (Color a) where
 methodOne = myEqual 

instance (Joker a, Eq a) => Joker (MyList a) where
 methodOne = myEqual
 methodTwo x y = if y == True then Red x else Blue x

instance (Joker a, Eq a, Eq b) => Joker (MPList a b)
