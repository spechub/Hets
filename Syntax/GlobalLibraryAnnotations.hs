
{- HetCATS/Syntax/GlobalLibraryAnnotations.hs
   $Id$
   Author: Christian Maeder
   Year:   2002

   A module to extract GlobalAnnos from libraries

-}

module Syntax.GlobalLibraryAnnotations where

import Common.GlobalAnnotations(GlobalAnnos)
import Common.GlobalAnnotationsFunctions(emptyGlobalAnnos, addGlobalAnnos)
import Syntax.AS_Library(LIB_DEFN(Lib_defn))

initGlobalAnnos :: LIB_DEFN -> GlobalAnnos
initGlobalAnnos ld = setGlobalAnnos emptyGlobalAnnos ld

setGlobalAnnos :: GlobalAnnos -> LIB_DEFN -> GlobalAnnos
setGlobalAnnos ga ld = addGlobalAnnos ga annos
    where annos = case ld of Lib_defn _ _ _ as -> as	  
