module Dummy where
import Prelude (undefined, Show, Eq, Ord, Bool)
import MyLogic
 
data FiniteSet a1 = FiniteSet
                  deriving (Show, Eq, Ord)
 
_2_P_2 :: (FiniteSet a, FiniteSet a) -> FiniteSet a
_2_P_2 = undefined
 
_2_M_2 :: (FiniteSet a, FiniteSet a) -> FiniteSet a
_2_M_2 = undefined
 
_b_2_r :: a -> FiniteSet a
_b_2_r = undefined
 
_b_r :: FiniteSet a
_b_r = undefined
