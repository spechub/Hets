module HasCASLModul where
import Prelude (undefined)
 
data A_s = A_s
 
data A_t = A_t
 
_2_P_2 :: (A_s, A_s) -> A_t
_2_P_2 = undefined
 
x :: A_s
x = undefined
 
y :: A_t
y = _2_P_2 (x, x)
