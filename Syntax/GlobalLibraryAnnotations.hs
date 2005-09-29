{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  experimental
Portability :  non-portable (imports existential types) 

A module to extract GlobalAnnos from libraries

-}

module Syntax.GlobalLibraryAnnotations where

import Common.GlobalAnnotations
import Common.AnalyseAnnos
import Common.Result
import Syntax.AS_Library(LIB_DEFN(Lib_defn))

initGlobalAnnos :: LIB_DEFN -> Result GlobalAnnos
initGlobalAnnos ld = setGlobalAnnos emptyGlobalAnnos ld

setGlobalAnnos :: GlobalAnnos -> LIB_DEFN -> Result GlobalAnnos
setGlobalAnnos ga ld = addGlobalAnnos ga annos
    where annos = case ld of Lib_defn _ _ _ as -> as      
