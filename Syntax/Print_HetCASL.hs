
{- HetCATS/Print_HetCASL.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   A module to abstract away GlobalAnnos and such things from the
   Write-Module.

   todo:
     - use optional argument of renderText and renderLatex for line_length.

-}

module Print_HetCASL where

import Common.Lib.Pretty
import PrettyPrint
import PPUtils (calc_line_length)
import GlobalAnnotationsFunctions(emptyGlobalAnnos)
import GlobalLibraryAnnotations

import AS_Library
import Print_AS_Library

printLIB_DEFN_text :: LIB_DEFN -> String
printLIB_DEFN_text ld = renderText Nothing $ printText ga ld
    where ga = initGlobalAnnos ld

default_latex_line_length :: Maybe Int
default_latex_line_length = -- Nothing
   Just $ calc_line_length "396.0pt"

printLIB_DEFN_latex :: LIB_DEFN -> String
printLIB_DEFN_latex ld = 
    renderLatex default_latex_line_length $ printLatex ga ld
    where ga = initGlobalAnnos ld

printLIB_DEFN_debugLatex :: LIB_DEFN -> String
printLIB_DEFN_debugLatex ld = 
    debugRenderLatex default_latex_line_length $ printLatex ga ld
    where ga = initGlobalAnnos ld


printText0_eGA :: forall a . (PrettyPrint a) => a -> Doc
printText0_eGA x = printText0 emptyGlobalAnnos x
