{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  experimental
Portability :  non-portable (imports existential types) 

A module to abstract away GlobalAnnos and such things from the
   Write-Module.

   todo:
     - use optional argument of renderText and renderLatex for line_length.

-}

module Syntax.Print_HetCASL where

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PrintLaTeX
import Common.LaTeX_utils (calc_line_length)
import Common.GlobalAnnotations(emptyGlobalAnnos,GlobalAnnos)

import Syntax.AS_Library
import Syntax.Print_AS_Library()
import Syntax.LaTeX_AS_Library()

data PrintMode = PMtext | PMlatex | PMdebugLatex

printLIB_DEFN_mode :: PrintMode -> GlobalAnnos -> LIB_DEFN -> String
printLIB_DEFN_mode m ga ld = 
    let doc = case m of 
              PMtext -> printText0  ga ld
              _      -> printLatex0 ga ld
        rend = (case m of 
                PMtext -> renderText Nothing
                PMlatex -> renderLatex default_latex_line_length
                PMdebugLatex -> debugRenderLatex default_latex_line_length)
    in rend doc
         {- -- $$ printText0 ga r -}
  -- print the whole result in this way causes LaTeX problems:
  -- not every line break gets an comment out (%) for LaTeX !!!

default_latex_line_length :: Maybe Int
default_latex_line_length = -- Nothing
   Just $ calc_line_length "345.0pt"
        -- for svmono you need 336.0pt

printLIB_DEFN_text, printLIB_DEFN_latex, printLIB_DEFN_debugLatex 
    :: GlobalAnnos -> LIB_DEFN -> String
printLIB_DEFN_text = printLIB_DEFN_mode PMtext
printLIB_DEFN_latex = printLIB_DEFN_mode PMlatex
printLIB_DEFN_debugLatex = printLIB_DEFN_mode PMdebugLatex


printText0_eGA :: forall a . (PrettyPrint a) => a -> Doc
printText0_eGA x = printText0 emptyGlobalAnnos x
