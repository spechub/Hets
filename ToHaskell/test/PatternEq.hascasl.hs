module HasCASLModul where
import Prelude (undefined)
 
data A_s = A_s
 
data A_t = A_t
 
a :: A_s
a = undefined
 
b :: A_s
b = a
 
c :: A_t
c = snd ((x :: A_s), (y :: A_t))
 
snd :: (A_s, A_t) -> A_t
snd = \ (x, y) -> (y :: A_t)
 
x :: A_s
x = undefined
 
y :: A_t
y = undefined
