module HasCASLModul where
import Prelude (undefined)
 
type Pred a = a -> ()
 
type Unit = ()
 
type A_s = A_t
 
data A_t = A_t
 
_2_P_23 :: A_t -> A_t -> A_t
_2_P_23 = undefined
 
_2_P_22 :: (A_t, A_t) -> A_t
_2_P_22 = undefined
 
_2_P_2 :: (A_s, A_s) -> A_s
_2_P_2 = undefined
 
_2_D_B_2 :: ((), ()) -> ()
_2_D_B_2 = undefined
 
_2_L_I_2_L_I_2 :: (A_s, A_s, A_s) -> A_s
_2_L_I_2_L_I_2 = undefined
 
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
 
a2 :: A_t
a2 = undefined
 
a :: A_s
a = undefined
 
b2 :: A_t
b2 = undefined
 
b :: A_s
b = undefined
 
c :: A_s
c = _2_P_2 (a, b)
 
d :: A_s
d = _2_P_2 (a, a)
 
def_2 :: a -> ()
def_2 = undefined
 
e :: (A_s, A_s) -> A_s
e = _2_P_2
 
f :: (A_s, A_s) -> A_s
f = _2_P_2
 
g :: (A_s, A_s)
g = (a, b)
 
h :: A_s
h = _2_P_2 (a, b)
 
i :: A_s
i = _2_P_2 ((a :: A_s), (b :: A_s))
 
i1 :: A_s
i1 = incr a
 
i2 :: A_s
i2 = incr a
 
i3 :: A_s
i3 = incr a
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
incr :: A_s -> A_s
incr = undefined
 
l1 :: A_s
l1 = _2_L_I_2_L_I_2 (a, b, c)
 
l2 :: (A_s, A_s, A_s) -> A_s
l2 = _2_L_I_2_L_I_2
 
l3 :: A_s
l3 = _2_L_I_2_L_I_2 (a, b, c)
 
l4 :: A_s
l4 = _2_L_I_2_L_I_2 (a, b, c)
 
l5 :: (A_s, A_s, A_s)
l5 = (a, b, c)
 
not_2 :: () -> ()
not_2 = undefined
 
x :: A_s
x = undefined
 
y :: A_s
y = _2_L_I_2_L_I_2 (a, (x :: A_s), (a :: A_s))
 
z :: A_s
z = _2_P_2 ((x :: A_s), ((x :: A_t) :: A_s))
