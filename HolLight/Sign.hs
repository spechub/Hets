{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HolLight/Sign.hs
Description :  HolLight signature
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module HolLight.Sign where

import Data.Typeable
import qualified Data.HashMap.Lazy as Map
import Common.DocUtils
import Common.Doc
import Common.Result
import HolLight.Term
import HolLight.Helper

data Sign = Sign { types :: Map.HashMap String Int
                 , ops :: Map.HashMap String HolType }
  deriving (Eq, Ord, Show, Typeable)

prettyTypes :: Map.HashMap String Int -> Doc
prettyTypes = ppMap text (\ i -> if i < 1 then empty else parens (pretty i))
  (const id) sepByCommas (<>)

instance Pretty Sign where
  pretty s = keyword "types" <+> prettyTypes (types s)
    $++$ ppMap text ppPrintType
         (const id) vcat (\ a -> (a <+> colon <+>)) (ops s)

emptySig :: Sign
emptySig = Sign {types = Map.empty, ops = Map.empty }

isSubSig :: Sign -> Sign -> Bool
isSubSig s1 s2 = types s1 `Map.isSubmapOf` types s2
  && ops s1 `Map.isSubmapOf` ops s2

sigUnion :: Sign -> Sign -> Result Sign
sigUnion (Sign {types = t1, ops = o1})
         (Sign {types = t2, ops = o2}) =
  return Sign {types = t1 `Map.union` t2, ops = o1 `Map.union` o2}
