{-# OPTIONS -fglasgow-exts #-}
module CombLogic where

import ModalLogic
import Data.List

data Box b c = Box b (Boole c)
{-
data BBox b c = BBox b (Boole c) (Boole c)

data K_KD = K_KD (Box K_u KD_K)
data KD_K = KD_K (Box KD_u K_KD)

data K_u = K_u deriving (Show, Eq)
data KD_u = KD_u deriving (Show, Eq)
-}

{- | Class for Formulas where 
 -       a is the "input" logic type
 -       b is the index type corresponding to a
 -       c is the "result" logic type
 -}
class Form a b c | a->b, a->c where
  extract :: Form a b c => a -> Box b c
  provable :: Form a b c => Boole a -> Bool

--instance Form K_KD K_u KD_K where
--instance Form (K (KD l)) K_u (KD l) where
--instance Eq l => Form (K (KD l)) (KD l) where
instance Eq l => Form (K l) () l where
  extract (K f) = Box () f
  {-
                  case f of
                    Not g   -> extract (K g)
                    And g h -> (extract (K g)) `union` (extract (K h))
                    At a    -> [a]
                    _       -> []
   -}

--instance Eq l => Form (KD (K l)) (K l) where
instance Eq l => Form (KD l) () l where
  extract (KD f) = Box () f
  {-
                   case f of
                     Not g   -> extract (KD g)
                     And g h -> (extract (KD g)) `union` (extract (KD h))
                     At a    -> [a]
                     _       -> []
   -}

--instance Form KD_K KD_u K_KD -- where
--instance Form (KD (K l)) KD_u (K l) -- where
instance Eq l => Form (G l) Int l where
  extract (G i f) = Box i f
