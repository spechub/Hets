{-# OPTIONS -fglasgow-exts #-}
module CombLogic where

import ModalLogic
import Data.List

data Box b c = Box b (Boole c)
-- data BBox b c = BBox b (Boole c) (Boole c)

{- | Class for Formulas where
 -       a is the "input" logic type
 -       b is the index type corresponding to a
 -       c is the "result" logic type
 -}
class Form a b c | a->b, a->c where
  extract :: Form a b c => a -> Box b c

instance Eq l => Form (K l) () l where
  extract (K f) = Box () f

instance Eq l => Form (KD l) () l where
  extract (KD f) = Box () f

instance Eq l => Form (G l) Int l where
  extract (G i f) = Box i f

