module HasCASLModul where
import Prelude (undefined)
 
type Pred a = a -> ()
 
type Unit = ()
 
data A__2_T_2 a1 a2 = A__2_T_2
 
data A__2_M_M_G_2 a1 a2 = A__2_M_M_G_2
 
data A__2_M_M_G_Q_2 a1 a2 = A__2_M_M_G_Q_2
 
data A__2_M_G_2 a1 a2 = A__2_M_G_2
 
data A__2_M_G_Q_2 a1 a2 = A__2_M_G_Q_2
 
_2_S_B_2 :: ((), ()) -> ()
_2_S_B_2 = undefined
 
_2_L_R_G_2 :: ((), ()) -> ()
_2_L_R_G_2 = undefined
 
_2_R_2 :: (a, a) -> ()
_2_R_2 = undefined
 
_2_R_G_2 :: ((), ()) -> ()
_2_R_G_2 = undefined
 
_2_Re_R_2 :: (a, a) -> ()
_2_Re_R_2 = undefined
 
_2_B_S_2 :: ((), ()) -> ()
_2_B_S_2 = undefined
 
_2if_2 :: ((), ()) -> ()
_2if_2 = undefined
 
_2when_2else_2 :: (a, (), a) -> a
_2when_2else_2 = undefined
 
def_2 :: a -> ()
def_2 = undefined
 
eq :: (Bool, Bool) -> Bool
 
false :: ()
false = undefined
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
le :: (Bool, Bool) -> Bool
 
ne :: (Bool, Bool) -> Bool
 
neg :: Bool -> Bool
 
not_2 :: () -> ()
not_2 = undefined
 
true :: ()
true = undefined
 
vee :: (Bool, Bool) -> Bool
 
wedge :: (Bool, Bool) -> Bool
 
data Bool = True
          | False
neg x
  = case x of
        False -> True
        True -> False
wedge (x, y)
  = case (x, y) of
        (False, False) -> False
        (True, False) -> False
        (False, True) -> False
        (True, True) -> True
vee (x, y) = neg (wedge (neg x, neg y))
le (x, y) = vee (neg x, y)
eq (x, y) = wedge (le (x, y), le (y, x))
ne (x, y) = wedge (vee (x, y), neg (wedge (x, y)))
