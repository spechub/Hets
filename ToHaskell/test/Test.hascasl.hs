module HasCASLModul where
import Prelude (undefined, Show)
 
data B = B
       deriving Show
 
data C = C
       deriving Show
 
data Int = Int
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
 
type A_s = B
 
_P :: (AT, B) -> C
_P = undefined
 
_2_S_B_2 :: ((), ()) -> ()
_2_S_B_2 = undefined
 
_2_L_E_G_2 :: ((), ()) -> ()
_2_L_E_G_2 = undefined
 
_2_E_2 :: (a, a) -> ()
_2_E_2 = undefined
 
_2_E_G_2 :: ((), ()) -> ()
_2_E_G_2 = undefined
 
_2_Ee_E_2 :: (a, a) -> ()
_2_Ee_E_2 = undefined
 
_2_B_S_2 :: ((), ()) -> ()
_2_B_S_2 = undefined
 
_2if_2 :: ((), ()) -> ()
_2if_2 = undefined
 
_2when_2else_2 :: (a, (), a) -> a
_2when_2else_2 = undefined
 
def_2 :: a -> ()
def_2 = undefined
 
f0 :: C -> C
f0 = undefined
 
f :: B -> B
f = undefined
 
false :: ()
false = undefined
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
not_2 :: () -> ()
not_2 = undefined
 
s1 :: AT -> Int
s1 = undefined
 
s2 :: AT -> B
s2 = undefined
 
true :: ()
true = undefined
 
data AT = A !(Int, B)
        deriving Show
