module HasCASLModul where
import Prelude (undefined)
 
data Unit = Unit
 
data A_bool = A_true
	    | A_false
 
a :: Unit
a = case l of
	A_true -> ()
	A_false -> ()
 
b2 :: Unit -> Unit
b2 = \ x -> ()
 
b :: Unit
b = let x = A_true
	y = A_false
	z = (x :: A_bool)
      in ()
 
l :: A_bool
l = undefined
