
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Some functions for building and accessing the datastructures 
   of GlobalAnnotations. This module should avoid further cyclic
   dependencies.

   todo:

-}


module GlobalAnnotationsFunctions 
    (emptyGlobalAnnos,initGlobalAnnos,setGlobalAnnos) 
    where

import Id
import AS_Library
import AS_Annotation
import GlobalAnnotations

import Graph
import FiniteMap

emptyGlobalAnnos :: GlobalAnnos
emptyGlobalAnnos = GA empty emptyFM emptyFM []

initGlobalAnnos :: LIB_DEFN -> GlobalAnnos
initGlobalAnnos ld = setGlobalAnnos emptyGlobalAnnos ld

setGlobalAnnos :: GlobalAnnos -> LIB_DEFN -> GlobalAnnos
setGlobalAnnos ga ld =
    ga { prec_annos    = store_prec_annos    (prec_annos  ga)   annos
       , assoc_annos   = store_assoc_annos   (assoc_annos ga)   annos
       , display_annos = store_display_annos (display_annos ga) annos
       , literal_annos = store_literal_annos (literal_annos ga) annos
       }
    where annos = case ld of Lib_defn _ _ _ as -> as	  

store_prec_annos :: PrecedenceGraph -> [Annotation] -> PrecedenceGraph
store_prec_annos pgr ans = pgr
{-	  precA an = case an of
		     Prec_anno _ _ _ _ -> True
        	     _                 -> False
	-}

store_assoc_annos :: AssocMap ->  [Annotation] -> AssocMap
store_assoc_annos am ans = addListToFM am assocs
    where assocs = concat $ map conn $ filter assocA ans
	  conn (Lassoc_anno is _) = map (conn' GlobalAnnotations.Left)  is
	  conn (Rassoc_anno is _) = map (conn' GlobalAnnotations.Right) is
	  conn _ = error "filtering isn't implented correct"
	  conn' sel i = (i,sel)
	  assocA an = case an of
		       Lassoc_anno _ _ -> True
		       Rassoc_anno _ _ -> True
		       _               -> False

store_display_annos :: DisplayMap -> [Annotation] -> DisplayMap
store_display_annos dm ans = addListToFM dm disps
    where disps = map conn $ filter displayA ans
	  conn (Display_anno i sxs _) = (i,sxs)
	  conn _ = error "filtering isn't implemented correct"
	  displayA an = case an of
		        Display_anno _ _ _ -> True
		        _                  -> False

store_literal_annos :: [Literal_Annos] -> [Annotation] -> [Literal_Annos]
store_literal_annos la _ = la