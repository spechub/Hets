{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
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
import Common.PPUtils (calc_line_length)
import Common.GlobalAnnotations(emptyGlobalAnnos)
import Common.ConvertGlobalAnnos
import Common.Result
import Syntax.GlobalLibraryAnnotations

import Syntax.AS_Library
import Syntax.Print_AS_Library
import Debug.Trace

data PrintMode = PMtext | PMlatex | PMdebugLatex

printLIB_DEFN_mode :: PrintMode -> LIB_DEFN -> String
printLIB_DEFN_mode m ld = 
    let r@(Result ds mga) = initGlobalAnnos ld
	ga = case mga of Nothing -> emptyGlobalAnnos
			 Just g -> g
	doc = case m of 
		     PMtext -> printText0 ga ld
		     _ -> printLatex0 ga ld
	in (case m of 
		 PMtext -> renderText Nothing
		 PMlatex -> renderLatex default_latex_line_length
		 PMdebugLatex -> debugRenderLatex default_latex_line_length)
	(if null ds then doc 
	 else trace (show $ vcat $ map (printText0 ga) ds) doc 
	 {- -- $$ printText0 ga r -})
  -- print the whole result in this way causes LaTeX problems:
  -- not every line break gets an comment out (%) for LaTeX !!!

default_latex_line_length :: Maybe Int
default_latex_line_length = -- Nothing
   Just $ calc_line_length "396.0pt"
	-- for svmono you need 336.0pt

printLIB_DEFN_text, printLIB_DEFN_latex, printLIB_DEFN_debugLatex 
    :: LIB_DEFN -> String
printLIB_DEFN_text = printLIB_DEFN_mode PMtext
printLIB_DEFN_latex = printLIB_DEFN_mode PMlatex
printLIB_DEFN_debugLatex = printLIB_DEFN_mode PMdebugLatex


printText0_eGA :: forall a . (PrettyPrint a) => a -> Doc
printText0_eGA x = printText0 emptyGlobalAnnos x
