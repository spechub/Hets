module HasCASLModul where
import Prelude (undefined, Show)
 
data Pair = Pair !(A_a, A_b)
          deriving Show
 
type Pred a = a -> ()
 
type Unit = ()
 
data A__2_T_2 a1 a2 = A__2_T_2
                    deriving Show
 
data A__2_M_M_G_2 a1 a2 = A__2_M_M_G_2
                        deriving Show
 
data A__2_M_M_G_Q_2 a1 a2 = A__2_M_M_G_Q_2
                          deriving Show
 
data A__2_M_G_2 a1 a2 = A__2_M_G_2
                      deriving Show
 
data A__2_M_G_Q_2 a1 a2 = A__2_M_G_Q_2
                        deriving Show
 
data A_a = A_a
         deriving Show
 
data A_b = A_b
         deriving Show
 
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
 
f :: (A_a, A_b) -> Pair
f = \ (a, b) -> Pair (a, b)
 
false :: ()
false = undefined
 
g :: Pair -> A_a
g = \ (Pair (a, b)) -> a
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
not_2 :: () -> ()
not_2 = undefined
 
true :: ()
true = undefined
