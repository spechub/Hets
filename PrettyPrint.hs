-- needs -package text 

{- HetCATS/PrettyPrint.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This class needs to be instantiated for every datastructure in AS_*
   for LaTeX and isolatin-1 pretty printing. It is only neccessary to
   provide one isolatin-1 printing method for prototypes, but for real
   nice output you need to implement every method.

   todo:
     
-}

module PrettyPrint where

import Pretty

-- This type class allows pretty printing of instantiating Datatypes
-- for infomation on the predefined functions see above
class Show a => PrettyPrint a where
    printLatex, printLatex0, printText, printText0  :: a -> Doc
    printLatex0 a = printText0 a
    printLatex  a = printText  a
    printText  a = printText0 a


-- two Styles for Formatting (Standard is Style PageMode 100 1.5)
latexStyle, textStyle :: Style
latexStyle = style {lineLength=80, ribbonsPerLine= 1.7} 
-- maximum line length 80 with 47 printable chars (up to 33 indentation chars) 
textStyle = latexStyle

-- functions for producing IO printable Strings
renderLatex,renderText,renderLatexVerb :: Doc -> String

renderLatex d = renderStyle latexStyle d
-- this lacks some environment starting and closing LaTeX commands

renderLatexVerb d = renderStyle latexStyle d'
    where d' = text "\\begin{verbatim}" $+$ d $+$ text "\\end{verbatim}"

renderText d = renderStyle textStyle d

-- helpers ------------------------------------
