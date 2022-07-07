
module NeSyPatterns.ATC_Relation where

import ATerm.Lib
import qualified Data.Relation as Rel


instance (ShATermConvertible a, ShATermConvertible b, Ord a, Ord b) => ShATermConvertible (Rel.Relation a b) where
  toShATermAux att0 = toShATermAux att0 . Rel.toList
  fromShATermAux ix att0 = Rel.fromList <$> fromShATermAux ix att0

