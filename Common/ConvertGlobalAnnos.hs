{- |
Module      :  $Header$
Description :  convert global annotations to a list of annotations
Copyright   :  (c) Carsten Fischer and Uni Bremen 2003-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Convert global annotations to a list of annotations
-}

module Common.ConvertGlobalAnnos
  ( mergeGlobalAnnos
  , c_lit_an
  ) where

import Common.Id
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel
import Common.AnalyseAnnos
import Common.Result
import Common.Doc
import Common.DocUtils

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (partition, groupBy, sortBy)

instance Pretty GlobalAnnos where
    pretty = printGlobalAnnos

printGlobalAnnos :: GlobalAnnos -> Doc
printGlobalAnnos = printAnnotationList . convertGlobalAnnos

convertGlobalAnnos::GlobalAnnos->[Annotation]
convertGlobalAnnos ga = c_prec (prec_annos ga)
              ++ c_assoc (assoc_annos ga)
              ++ c_displ (display_annos ga)
              ++ c_lit_an (literal_annos ga)

mergeGlobalAnnos :: GlobalAnnos -> GlobalAnnos -> Result GlobalAnnos
mergeGlobalAnnos ga1 = addGlobalAnnos ga1 . convertGlobalAnnos

c_prec :: PrecedenceGraph -> [Annotation]
c_prec pg =
    let cs = Rel.sccOfClosure pg
    in map (\ l -> let (f, r) = splitAt (div (length l) 2) l in
                   Prec_anno BothDirections f r nullRange)
           (filter ((> 1) . length) $ map Set.toList cs)
       ++ map (\ l@((_, s) : _) ->
        Prec_anno Lower (map fst l) (Set.toList s) nullRange)
        (groupBy (\ a b -> snd a == snd b)
          $ sortBy (\ a b -> compare (snd a) $ snd b)
            $ Map.toList $ Rel.toMap $ Rel.transReduce $ Rel.irreflex
               $ Rel.collaps cs pg)

c_assoc :: AssocMap -> [Annotation]
c_assoc am =
    let (i1s, i2s) = partition ((== ALeft) . snd) $ Map.toList am
        -- [(Id,assEith)]
    in [Assoc_anno ALeft (map fst i1s) nullRange | not $ null i1s]
       ++ [Assoc_anno ARight (map fst i2s) nullRange | not $ null i2s ]

c_displ :: DisplayMap -> [Annotation]
c_displ dm =
    let m1 = Map.toList dm -- m1::[(Id,Map.Map Display_format [Token])]
        toStrTup (x, y) = (x, concatMap tokStr y)
        m2 = map (\ (x, m) -> (x, map toStrTup $ Map.toList m)) m1
        -- m2::[(ID,[(Display_format,String)])]
    in map (\ (i, x) -> Display_anno i x nullRange) m2

c_lit_an :: LiteralAnnos -> [Annotation]
c_lit_an la = let
  str = case string_lit la of
          Just (x, y) -> [String_anno x y nullRange]
          _ -> []
  lis = map (\ (br, (n, con)) -> List_anno br n con nullRange)
          $ Map.toList $ list_lit la
  number = case number_lit la of
             Just x -> [Number_anno x nullRange]
             _ -> []
  flo = case float_lit la of
          Just (a, b) -> [Float_anno a b nullRange]
          _ -> []
  in str ++ lis ++ number ++ flo
