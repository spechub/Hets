module HasCASLModul where
import Prelude (undefined, Show)
 
type Pred a = a -> ()
 
type Unit = ()
 
data A__2_T_2 = A__2_T_2
              deriving Show
 
data A__2_M_M_G_2 = A__2_M_M_G_2
                  deriving Show
 
data A__2_M_M_G_Q_2 = A__2_M_M_G_Q_2
                    deriving Show
 
data A__2_M_G_2 = A__2_M_G_2
                deriving Show
 
data A__2_M_G_Q_2 = A__2_M_G_Q_2
                  deriving Show
 
type A_s = A_t
 
data A_t = A_t
         deriving Show
 
_2_P_2 :: (A_s, A_s) -> A_s
_2_P_2 = undefined
 
_2_S_B_2 :: ((), ()) -> ()
_2_S_B_2 = undefined
 
_2_L_R_2_L_R_2 :: (A_s, A_s, A_s) -> A_s
_2_L_R_2_L_R_2 = undefined
 
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
 
a :: A_s
a = undefined
 
b :: A_s
b = undefined
 
c :: A_s
c = _2_P_2 ((a, b))
 
d :: A_s
d = _2_P_2 ((a, a))
 
def_2 :: a -> ()
def_2 = undefined
 
e :: (A_s, A_s) -> A_s
e = _2_P_2
 
f :: (A_s, A_s) -> A_s
f = _2_P_2
 
false :: ()
false = undefined
 
g :: (A_s, A_s)
g = (a, b)
 
h :: A_s
h = _2_P_2 ((a, b))
 
i :: A_s
i = _2_P_2 (((a :: A_s), (b :: A_s)))
 
i1 :: A_s
i1 = incr (a)
 
i2 :: A_s
i2 = incr (a)
 
i3 :: A_s
i3 = incr (a)
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
incr :: A_s -> A_s
incr = undefined
 
l1 :: A_s
l1 = _2_L_R_2_L_R_2 ((a, b, c))
 
l2 :: (A_s, A_s, A_s) -> A_s
l2 = _2_L_R_2_L_R_2
 
l3 :: A_s
l3 = _2_L_R_2_L_R_2 ((a, b, c))
 
l4 :: A_s
l4 = _2_L_R_2_L_R_2 ((a, b, c))
 
l5 :: (A_s, A_s, A_s)
l5 = (a, b, c)
 
not_2 :: () -> ()
not_2 = undefined
 
true :: ()
true = undefined
 
x :: A_s
x = undefined
 
y :: A_s
y = _2_L_R_2_L_R_2 ((a, (x :: A_s), (a :: A_s)))
 
z :: A_s
z = _2_P_2 (((x :: A_s), ((x :: A_t) :: A_s)))
