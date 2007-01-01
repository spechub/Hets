{- |
Module      :  $Header$
Description :  convert global annotations to a list of annotations
Copyright   :  (c) Carsten Fischer and Uni Bremen 2003-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Convert global annotations to a list of annotations
-}

module Common.ConvertGlobalAnnos where

import Common.Id
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.AnalyseAnnos
import Common.Result
import Common.Doc
import Common.DocUtils

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
mergeGlobalAnnos ga1 ga2 = addGlobalAnnos ga1 $ convertGlobalAnnos ga2

c_prec :: PrecedenceGraph -> [Annotation]
c_prec pg = let erg = Rel.toList pg
            in  map ( \ (x,y) -> Prec_anno (precRel pg x y) [x] [y] nullRange)
                    $ filter ( \ (x, y) -> x /= y) erg

c_assoc :: AssocMap -> [Annotation]
c_assoc am =
    let liste = Map.toList am -- [(Id,assEith)]
        i1s = [ i | (i,aE)<-liste, aE == ALeft]
        i2s = [ i | (i,aE)<-liste, aE == ARight]
    in (if null i1s then [] else [(Assoc_anno ALeft i1s nullRange)])
       ++ (if null i2s then [] else [(Assoc_anno ARight i2s nullRange)])

c_displ :: DisplayMap -> [Annotation]
c_displ dm =
    let m1 = Map.toList dm -- m1::[(Id,Map.Map Display_format [Token])]
        toStrTup = (\ (x,y) -> (x, concatMap tokStr y))
        m2 = map (\ (x,m) -> (x, map toStrTup (Map.toList m))) m1
        -- m2::[(ID,[(Display_format,String)])]
    in map (\ (i,x) -> Display_anno i x nullRange) m2

c_lit_an :: LiteralAnnos->[Annotation]
c_lit_an la = let str = case (string_lit la) of
                             Just (x,y) -> [String_anno x y nullRange]
                             _ -> []
                  lis = map (\ (br,(n,con)) -> List_anno br n con nullRange)
                         (Map.toList (list_lit la))
                  number = case (number_lit la) of
                                 Just x -> [Number_anno x nullRange]
                                 _ -> []
                  flo = case (float_lit la) of
                                 Just (a,b) -> [Float_anno a b nullRange]
                                 _ -> []
              in str++lis++number++flo
