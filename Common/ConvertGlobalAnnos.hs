{- |
Module      :  $Header$
Description :  convert global annotations to a list of annotations
Copyright   :  (c) Carsten Fischer and Uni Bremen 2003-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Convert global annotations to a list of annotations
-}

module Common.ConvertGlobalAnnos
  ( mergeGlobalAnnos
  , convertGlobalAnnos
  , convertLiteralAnnos
  , removeHetCASLprefixes
  ) where

import Common.Id
import Common.IRI
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel
import Common.AnalyseAnnos
import Common.Result
import Common.DocUtils

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (partition, groupBy, sortBy)
import Data.Ord
import Data.Function (on)

instance Pretty GlobalAnnos where
  pretty = printAnnotationList . convertGlobalAnnos . removeHetCASLprefixes

removeHetCASLprefixes :: GlobalAnnos -> GlobalAnnos
removeHetCASLprefixes ga = ga
  { prefix_map = Map.filter (not . null . iriScheme) $ prefix_map ga }

convertGlobalAnnos :: GlobalAnnos -> [Annotation]
convertGlobalAnnos ga = convertPrefixMap (prefix_map ga)
              ++ convertPrec (prec_annos ga)
              ++ convertAssoc (assoc_annos ga)
              ++ convertDispl (display_annos ga)
              ++ convertLiteralAnnos (literal_annos ga)

mergeGlobalAnnos :: GlobalAnnos -> GlobalAnnos -> Result GlobalAnnos
mergeGlobalAnnos ga1 = addGlobalAnnos ga1 . convertGlobalAnnos

convertPrec :: PrecedenceGraph -> [Annotation]
convertPrec pg =
    let cs = Rel.sccOfClosure pg
    in map (\ l -> let (f, r) = splitAt (div (length l) 2) l in
                   Prec_anno BothDirections f r nullRange)
           (filter ((> 1) . length) $ map Set.toList cs)
       ++ map (\ l ->
        Prec_anno Lower (map fst l) (Set.toList $ snd $ head l) nullRange)
        (groupBy ((==) `on` snd)
          $ sortBy (comparing snd)
            $ Map.toList $ Rel.toMap
               $ Rel.rmNullSets $ Rel.transReduce $ Rel.irreflex
               $ Rel.collaps cs pg)

convertAssoc :: AssocMap -> [Annotation]
convertAssoc am =
    let (i1s, i2s) = partition ((== ALeft) . snd) $ Map.toList am
        -- [(Id,assEith)]
    in [Assoc_anno ALeft (map fst i1s) nullRange | not $ null i1s]
       ++ [Assoc_anno ARight (map fst i2s) nullRange | not $ null i2s ]

convertDispl :: DisplayMap -> [Annotation]
convertDispl dm =
    let m1 = Map.toList dm -- m1::[(Id,Map.Map Display_format [Token])]
        toStrTup (x, y) = (x, concatMap tokStr y)
        m2 = map (\ (x, m) -> (x, map toStrTup $ Map.toList m)) m1
        -- m2::[(ID,[(Display_format,String)])]
    in map (\ (i, x) -> Display_anno i x nullRange) m2

convertLiteralAnnos :: LiteralAnnos -> [Annotation]
convertLiteralAnnos la = let
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

convertPrefixMap :: PrefixMap -> [Annotation]
convertPrefixMap pm =
  if Map.null pm then [] else [Prefix_anno (Map.toList pm) nullRange]
