module HasCASLModul where
import Prelude (undefined, Show)
 
type Pred a = a -> ()
 
type Unit = ()
 
data A__2_M_M_G_2 = A__2_M_M_G_2
		  deriving Show
 
data A__2_M_M_G_Q_2 = A__2_M_M_G_Q_2
		    deriving Show
 
data A__2_M_G_2 = A__2_M_G_2
		deriving Show
 
data A__2_M_G_Q_2 = A__2_M_G_Q_2
		  deriving Show
 
data A__2_m_2 = A__2_m_2
	      deriving Show
 
data A_bool = True
	    | False
	    deriving Show
 
_2_D_B_2 :: ((), ()) -> ()
_2_D_B_2 = undefined
 
_2_L_I_G_2 :: ((), ()) -> ()
_2_L_I_G_2 = undefined
 
_2_I_2 :: (a, a) -> ()
_2_I_2 = undefined
 
_2_I_G_2 :: ((), ()) -> ()
_2_I_G_2 = undefined
 
_2_Ie_I_2 :: (a, a) -> ()
_2_Ie_I_2 = undefined
 
_2_B_D_2 :: ((), ()) -> ()
_2_B_D_2 = undefined
 
_2if_2 :: ((), ()) -> ()
_2if_2 = undefined
 
_2when_2else_2 :: (a, (), a) -> a
_2when_2else_2 = undefined
 
a :: A_bool
a = True
 
b2 :: A_bool -> A_bool
b2 = \ x -> (x :: A_bool)
 
b :: A_bool
b = let x = True
	y = False
	z = (x :: A_bool)
      in True
 
def_2 :: a -> ()
def_2 = undefined
 
false :: ()
false = undefined
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
not_2 :: () -> ()
not_2 = undefined
 
notA :: A_bool
notA
  = case a of
	True -> False
	False -> True
 
true :: ()
true = undefined
