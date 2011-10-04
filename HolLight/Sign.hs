{- |
Module      :  $Header$
Description :  HolLight signature
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module HolLight.Sign where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.DocUtils
import Common.Doc
import Common.Result
import HolLight.Term
import HolLight.Helper

-- types should store the type kinds for every type constructor
data Sign = Sign { types :: Map.Map String Int
                 , ops :: Map.Map String HolType
                 , typeVars :: Set.Set String }
  deriving (Eq, Ord, Show)

pretty_types :: Map.Map String Int -> Doc
pretty_types = ppMap text (\ i -> if i < 1 then empty else parens (pretty i))
  (const id) sepByCommas (<>)

instance Pretty Sign where
  pretty s = keyword "types" <+> pretty_types (types s)
    $++$ keyword "typeVars" <+> (ppSet text (const id) sepByCommas (typeVars s))
    $++$ ppMap text pp_print_type
         (const id) vcat (\ a -> (a <+> colon <+>)) (ops s)

emptySig :: Sign
emptySig = Sign {types = Map.empty, ops = Map.empty, typeVars = Set.empty}

isSubSig :: Sign -> Sign -> Bool
isSubSig s1 s2 = types s1 `Map.isSubmapOf` types s2
  && ops s1 `Map.isSubmapOf` ops s2

sigUnion :: Sign -> Sign -> Result Sign
sigUnion (Sign {types = t1, ops = o1, typeVars = tv1})
         (Sign {types = t2, ops = o2, typeVars = tv2}) =
  return Sign {types = Map.union t1 t2, ops = Map.union o1 o2, typeVars = Set.union tv1 tv2}
