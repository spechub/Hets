module MyLogic (_2_S_B_2, _2_L_E_G_2, _2_E_2
	       , _2_E_G_2, _2_Ee_E_2, _2_B_S_2
	       , _2if_2, _2when_2else_2, if_2then_2else_2
	       , not_2, true, false) where

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
 
false :: Bool
false = False

true :: Bool
true = True
