
{- HetCATS/Print_HetCASL.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   A module to abstract away GlobalAnnos and such things from the
   Write-Module.

   todo:
 

-}

module Print_HetCASL where

import PrettyPrint
import GlobalAnnotations
import GlobalAnnotationsFunctions

import AS_Library
import Print_AS_Library

printLIB_DEFN_text :: LIB_DEFN -> String
printLIB_DEFN_text ld = renderText $ printText ga ld
    where ga = initGlobalAnnos ld

printLIB_DEFN_latex :: LIB_DEFN -> String
printLIB_DEFN_latex ld = renderLatex $ printLatex ga ld
    where ga = initGlobalAnnos ld
