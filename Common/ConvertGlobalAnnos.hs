
{- |
Module      :  $Header$
Copyright   :  (c) Carsten Fischer and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
convert global annotations to a list of annotations

-}

module Common.ConvertGlobalAnnos where

import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.GlobalAnnotationsFunctions

convertGlobalAnnos::GlobalAnnos->[Annotation]
convertGlobalAnnos ga = c_prec (prec_annos ga) 
	      ++ c_assoc (assoc_annos ga)
	      ++ c_displ (display_annos ga)
              ++ c_lit_an (literal_annos ga)
	      ++ c_lit_map (literal_map ga)

-- Achtung noch nicht fertig
c_prec::PrecedenceGraph->[Annotation]
c_prec pg = -- [Prec_anno Lower [] [] []]
            let erg = Rel.toList pg -- [(Id,???)]
            in  map ( \ (x,y) -> Prec_anno (precRel pg x y) [x] [y] []) erg  

c_assoc::AssocMap->[Annotation]
c_assoc am = 
    let liste = Map.toList am -- [(Id,assEith)]
        i1s = [ i | (i,aE)<-liste, aE == ALeft]
        i2s = [ i | (i,aE)<-liste, aE == ARight]
    in [(Assoc_anno ALeft i1s []),(Assoc_anno ARight i2s [])]

c_displ::DisplayMap->[Annotation]
c_displ dm =
    let m1 = Map.toList dm -- m1::[(Id,Map.Map Display_format String)] 
        m2 = map (\ (x,m) -> (x, Map.toList m)) m1
	-- m2::[(ID,[(Display_format,String)])]
    in map (\ (i,[d_f,str]) -> Display_anno i [d_f,str] []) m2
		   
c_lit_an::LiteralAnnos->[Annotation]
c_lit_an la = let str = case (string_lit la) of
			     Just (x,y) -> [String_anno x y []]
			     _ -> []
                  lis = map (\ (br,n,con) -> List_anno br n con []) 
                         (Set.toList (list_lit la))
                  number = case (number_lit la) of
				 Just x -> [Number_anno x []]
				 _ -> []
                  flo = case (float_lit la) of
				 Just (a,b) -> [Float_anno a b []]
                                 _ -> []
              in str++lis++number++flo


-- Only a Dummy
c_lit_map::LiteralMap->[Annotation]
c_lit_map _lm = []

{-
c_lit_map lm = let liste = Map.toList lm -- [(Id,LiteralType)]
	       in concat $ map (\ (i,lt) -> checkLT i lt) liste


checkLT::Id->LiteralType->[Annotation]
checkLT i lt  = case lt of
			StringCons x -> [String_anno i x []]
			ListCons x y -> [List_anno i x y []]
			Number       -> [Number_anno i []]
			Floating     -> [Float_anno i i []] -- Achtung, falsch!
			_ -> []
-}