module HasCASLModul where
import Prelude (undefined, Show)
 
data Bool = True
          | False
          deriving Show
 
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
eq
  = \ (x, y) ->
      wedge
        ((le (((x :: Bool), (y :: Bool))),
          le (((y :: Bool), (x :: Bool)))))
 
false :: ()
false = undefined
 
if_2then_2else_2 :: ((), a, a) -> a
if_2then_2else_2 = undefined
 
le :: (Bool, Bool) -> Bool
le = \ (x, y) -> vee ((neg ((x :: Bool)), (y :: Bool)))
 
ne :: (Bool, Bool) -> Bool
ne
  = \ (x, y) ->
      wedge
        ((vee (((x :: Bool), (y :: Bool))),
          neg (wedge (((x :: Bool), (y :: Bool))))))
 
neg :: Bool -> Bool
neg
  = \ x ->
      case (x :: Bool) of
          False -> True
          True -> False
 
not_2 :: () -> ()
not_2 = undefined
 
true :: ()
true = undefined
 
vee :: (Bool, Bool) -> Bool
vee
  = \ (x, y) -> neg (wedge ((neg ((x :: Bool)), neg ((y :: Bool)))))
 
wedge :: (Bool, Bool) -> Bool
wedge
  = \ (x, y) ->
      case ((x :: Bool), (y :: Bool)) of
          (False, False) -> False
          (True, False) -> False
          (False, True) -> False
          (True, True) -> True
