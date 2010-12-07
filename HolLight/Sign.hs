module HolLight.Sign where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import Common.DocUtils
import Common.Doc
import HolLight.Term
import HolLight.Helper

data Sign = Sign { types :: Set.Set HolType
                 , ops :: Map.Map String (Set.Set HolType) }
  deriving (Eq, Ord, Show)

pretty_type_list :: [HolType] -> Doc
pretty_type_list tps = hcat (List.intersperse (text ", ")
                             (map (\tp -> hcat
                                [text "`:",pp_print_type tp,text "`"])
                             tps))

instance Pretty Sign where
  pretty s = let tps = Set.toList (types s) in
             let opsM = ops s
             in hcat [text "Signature = { ", vcat $ (hcat [text "types = {",pretty_type_list tps,text "}"]):(
               Map.foldWithKey (\k v a ->
                 (hcat [text "type_of(",text k, text ") = {",
                        pretty_type_list (Set.toList v),text "}"]):a) [] opsM
             ), text " }"]

emptySig :: Sign
emptySig = Sign{types = Set.empty, ops = Map.empty}

isSubSig :: Sign -> Sign -> Bool
isSubSig s1 s2 = (types s1) `Set.isSubsetOf` (types s2)
