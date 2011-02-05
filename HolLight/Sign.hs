module HolLight.Sign where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import Common.DocUtils
import Common.Doc
import Common.Result
import HolLight.Term
import HolLight.Helper

-- types should store the type kinds for every type constructor
data Sign = Sign { types :: Map.Map String Int
                 , ops :: Map.Map String (Set.Set HolType) }
  deriving (Eq, Ord, Show)

pretty_types :: Map.Map String Int -> Doc
pretty_types tps = hcat (List.intersperse (text ", ") (Map.foldWithKey (\k v a ->
                              (hcat [text "arity_of(`:", text k,text "`)=",text (show v)]):a) [] tps))

pretty_type_list :: [HolType] -> Doc
pretty_type_list tps = hcat (List.intersperse (text ", ")
                              (map (\tp -> hcat
  	                           [text "`:",pp_print_type tp,text "`"])
  	                        tps))

instance Pretty Sign where
  pretty s = let tps = types s in
             let opsM = ops s
             in hcat [text "Signature = { ", vcat $ (hcat [text "types = {",pretty_types tps,text "}"]):(
               Map.foldWithKey (\k v a ->
                 (hcat [text "type_of(",text k, text ") = {",
                        pretty_type_list (Set.toList v),text "}"]):a) [] opsM
             ), text " }"]

emptySig :: Sign
emptySig = Sign{types = Map.empty, ops = Map.empty}

isSubSig :: Sign -> Sign -> Bool
isSubSig s1 s2 = ((types s1) `Map.isSubmapOf` (types s2)) && ((ops s1) `Map.isSubmapOf` (ops s2))

sigUnion :: Sign -> Sign -> Result Sign
sigUnion (Sign {types = t1,ops = o1}) (Sign {types = t2, ops = o2}) = return $ Sign {types=Map.union t1 t2,ops=Map.union o1 o2}
