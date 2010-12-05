module HolLight.Sign where

import qualified Data.Set as Set
import qualified Data.List as List
import Common.DocUtils
import Common.Doc
import HolLight.Term
import HolLight.Helper

data Sign = Sign { types :: Set.Set HolType }
  deriving (Eq, Ord, Show)

instance Pretty Sign where
  pretty s = let tps = Set.toList (types s)
             in hcat ((text "`:"):(List.intersperse (text ", ")
                      (map pp_print_type tps))++[text "`"])

emptySig :: Sign
emptySig = Sign{types = Set.empty}

isSubSig :: Sign -> Sign -> Bool
isSubSig s1 s2 = (types s1) `Set.isSubsetOf` (types s2)
