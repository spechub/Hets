{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

   for the execution of translated HasCASL program equations
-}

module MyLogic where

type Unit = Bool
type Pred a = a -> Bool

bottom :: a
bottom = undefined

a___2_S_B_2 :: (Bool, Bool) -> Bool
a___2_S_B_2 = uncurry (&&)
 
a___2_L_E_G_2 :: (Bool, Bool) -> Bool
a___2_L_E_G_2 = uncurry (==)
 
a___2_E_2 :: Eq a => (a, a) -> Bool
a___2_E_2 = uncurry (==)
 
a___2_E_G_2 :: (Bool, Bool) -> Bool
a___2_E_G_2 (a, b) = if a then b else True
 
a___2_Ee_E_2 :: Eq a => (a, a) -> Bool
a___2_Ee_E_2 = uncurry (==)
 
a___2_B_S_2 :: (Bool, Bool) -> Bool
a___2_B_S_2 = uncurry (||) 

a___2if_2 :: (Bool, Bool) -> Bool
a___2if_2 (a, b) = if b then a else True

a___2when_2else_2 :: (a, Bool, a) -> a
a___2when_2else_2 (a, b, c) = if b then a else c 

not_2 :: Bool -> Bool
not_2 = not

def_2 :: a -> Bool
def_2 a = a `seq` True
 
false :: Bool
false = False

true :: Bool
true = True
