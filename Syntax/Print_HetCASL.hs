
{- HetCATS/Syntax/Print_HetCASL.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   A module to abstract away GlobalAnnos and such things from the
   Write-Module.

   todo:
     - use optional argument of renderText and renderLatex for line_length.

-}

module Syntax.Print_HetCASL where

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils (calc_line_length)
import Common.GlobalAnnotationsFunctions(emptyGlobalAnnos)
import Syntax.GlobalLibraryAnnotations

import Syntax.AS_Library
import Syntax.Print_AS_Library

printLIB_DEFN_text :: LIB_DEFN -> String
printLIB_DEFN_text ld = renderText Nothing $ printText0 ga ld
    where ga = initGlobalAnnos ld

default_latex_line_length :: Maybe Int
default_latex_line_length = -- Nothing
   Just $ calc_line_length "396.0pt"

printLIB_DEFN_latex :: LIB_DEFN -> String
printLIB_DEFN_latex ld = 
    renderLatex default_latex_line_length $ printLatex0 ga ld
    where ga = initGlobalAnnos ld

printLIB_DEFN_debugLatex :: LIB_DEFN -> String
printLIB_DEFN_debugLatex ld = 
    debugRenderLatex default_latex_line_length $ printLatex0 ga ld
    where ga = initGlobalAnnos ld


printText0_eGA :: forall a . (PrettyPrint a) => a -> Doc
printText0_eGA x = printText0 emptyGlobalAnnos x
