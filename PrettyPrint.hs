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

import Id
import Pretty
import GlobalAnnotations

-- This type class allows pretty printing of instantiating Datatypes
-- for infomation on the predefined functions see above
class Show a => PrettyPrint a where
    printLatex, printLatex0, printText, printText0 :: GlobalAnnos -> a -> Doc
    printLatex0 ga a = printText0 ga a
    printLatex  ga a = printText  ga a
    printText   ga a = printText0 ga a

-- copied instance from Id.hs (to avoid cyclic imports via GlobalAnnotations)
instance PrettyPrint Token where
 printText0 _ t = ptext (tokStr t)

instance PrettyPrint Id where
 printText0 _ i = text (showId i "")

-- some useful instances ---------------------------------------------
instance PrettyPrint String where
    printText0  _ = ptext
    printLatex0 _ = ptext

{-instance (PrettyPrint a) => PrettyPrint [a] where
    printText0  ga l = cat $ map (printText0  ga) l
    printLatex0 ga l = cat $ map (printLatex0 ga) l
    printText   ga l = cat $ map (printText   ga) l
    printLatex  ga l = cat $ map (printLatex  ga) l
-}
----------------------------------------------------------------------
-- two Styles for Formatting (Standard is Style PageMode 100 1.5)
latexStyle, textStyle :: Style
latexStyle = style {lineLength=80, ribbonsPerLine= 1.19} 
-- maximum line length 80 with 67 printable chars (up to 13 indentation chars) 
textStyle = latexStyle

-- functions for producing IO printable Strings
renderLatex,renderText,renderLatexVerb :: Doc -> String

renderLatex d = renderStyle latexStyle d
-- this lacks some environment starting and closing LaTeX commands

renderLatexVerb d = renderStyle latexStyle d'
    where d' = text "\\begin{verbatim}" $+$ d $+$ text "\\end{verbatim}"

renderText d = renderStyle textStyle d

-- helpers ------------------------------------
sp_hang :: Doc -> Int -> Doc -> Doc
sp_hang d1 n d2 = cat [d1, nest n d2]

sp_brackets :: Doc -> Doc 
sp_brackets p = sp_hang (sp_hang lbrack 1 p) 0 rbrack

sp_braces :: Doc -> Doc 
sp_braces p = sp_hang (sp_hang lbrace 1 p) 0 rbrace

