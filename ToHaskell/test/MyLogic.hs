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

type Pred a = a -> Bool

_2_S_B_2 :: (Bool, Bool) -> Bool
_2_S_B_2 = uncurry (&&)
 
_2_L_E_G_2 :: (Bool, Bool) -> Bool
_2_L_E_G_2 = _2_E_2
 
_2_E_2 :: Eq a => (a, a) -> Bool
_2_E_2 = uncurry (==)
 
_2_E_G_2 :: (Bool, Bool) -> Bool
_2_E_G_2 (a, b) = if a then b else True
 
_2_Ee_E_2 :: Eq a => (a, a) -> Bool
_2_Ee_E_2 = _2_E_2
 
_2_B_S_2 :: (Bool, Bool) -> Bool
_2_B_S_2 = uncurry (||) 

_2if_2 :: (Bool, Bool) -> Bool
_2if_2 (a, b) = _2_E_G_2 (b, a)

_2when_2else_2 :: (a, Bool, a) -> a
_2when_2else_2 (a, b, c) = if b then a else c 

if_2then_2else_2 :: (Bool, a, a) -> a
if_2then_2else_2 (a, b, c) = if a then b else c 
 
not_2 :: Bool -> Bool
not_2 = not

def_2 :: a -> Bool
def_2 a = a `seq` True
 
false :: Bool
false = False

true :: Bool
true = True
