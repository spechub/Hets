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
    printLatex0 a = ptext "\\verb¦" <> printText0 a <> char '¦'
    printLatex  a = ptext "\\verb¦" <> printText  a <> char '¦'
    printText  a = printText0 a

{-    
-- two Styles for Formatting (Standard is Style PageMode 100 1.5)
latexStyle, asciiStyle :: Style
latexStyle = Style PageMode 80 1.7 
-- maximum line length 80 with 47 printable chars (up to 33 indentation chars) 
asciiStyle = latexStyle

-- functions for producing IO printable Strings
renderLatex, renderAscii :: Doc -> String
renderLatex d = renderStyle latexStyle d'
    where d' = d
-- this lacks some environment starting and closing LaTeX commands

renderAscii d = renderStyle asciiStyle d
-}

{-
-- helpers ------------------------------------
-- reduce nested \\verb; things
close_verb :: Doc -> Doc
close_verb Empty                 = Empty
close_verb (NilAbove doc)        = NilAbove (close_verb doc)
close_verb (TextBeside td i doc) = 
                 if is_verb td then 
		    TextBeside td i (remove_and_close_verb doc) 
		 else TextBeside td i (close_verb doc)
close_verb (Nest i doc)          = Nest i (close_verb doc)
close_verb d = d
-}

