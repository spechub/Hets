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

import Char (isSpace)

import Id
import Pretty
import GlobalAnnotations
import LaTeX_funs

import IOExts (trace)

-- This type class allows pretty printing of instantiating Datatypes
-- for infomation on the predefined functions see above
class Show a => PrettyPrint a where
    printLatex, printLatex0, printText, printText0 :: GlobalAnnos -> a -> Doc
    printLatex0 ga a = printText0 ga a
    printLatex  ga a = printLatex0  ga a
    printText   ga a = printText0 ga a

{-instance (PrettyPrint a) => PrettyPrint [a] where
    printText0  ga l = cat $ map (printText0  ga) l
    printLatex0 ga l = cat $ map (printLatex0 ga) l
    printText   ga l = cat $ map (printText   ga) l
    printLatex  ga l = cat $ map (printLatex  ga) l
-}
----------------------------------------------------------------------
-- two Styles for Formatting (Standard is Style PageMode 100 1.5)

latexStyle, textStyle :: Style
textStyle = style {lineLength=80, ribbonsPerLine= 1.19} 
-- maximum line length 80 with 67 printable chars (up to 13 indentation chars) 
latexStyle = textStyle {ribbonsPerLine = 1.2,lineLength = 121095}

latex_txt :: TextDetails -> String -> String
latex_txt (Chr c)   s  = c:s
latex_txt (Str s1)  s2
    | null s1        = s2
    | all isSpace s1 = sub_space s1 ++ s2
    | otherwise      = s1 ++ s2
latex_txt (PStr s1) s2 = -- case s1 of 
			 -- s | s == "[" || s == "PowerTheorems" 
			    --   -> trace ("gotcha " ++ s) (s1 ++ s2) 
			   -- | otherwise ->  
			       s1 ++ s2
-- | 
-- A constant for calculating indentation
indent_mult :: Int
indent_mult = 13

-- |
-- sub_space is a sophisticatecd way to determine the right
-- indentation. So therefor the latex_nest [5,6,7] are reserved for
-- this purpose

sub_space :: String -> String
sub_space s1 = -- trace ("number of Spaces " ++ show len_s1) $
    -- indent_sign ((len_s1 `mod` space_latex_width) `div` indent_mult) ++
	 replicate (len_s1 `div` space_latex_width) ' '
    where indent_sign x
	      | x - 15 >= 0 = indent_HC ++ indent_CA ++ indent_PA
	      | x - 12 >= 0 = indent_HC ++ indent_CA 
	      | x - 10 >= 0 = indent_HC ++ indent_PA
	      | x -  7 >= 0 = indent_HC
	      | x -  5 >= 0 = indent_CA
	      | x -  3 >= 0 = indent_PA
	      | otherwise  = "" 
	      where  indent_HC = "\\IndHC{}"
		     indent_CA = "\\IndCA{}"
 		     indent_PA = "\\IndPA{}"
          len_s1 :: Int
	  len_s1 = cntSpc s1 0
	  cntSpc [] l     = l
	  cntSpc (x:xs) l 
	      | x == '\t' = cntSpc xs (l+8)
	      | otherwise = cntSpc xs (l+1)
    {- add_space = if len_s1 `mod` space_latex_width > 0 
		      then "\\hspace{" ++ rem_space ++ "mm}"
		      else ""
	  rem_space = (\(s,f) -> reverse f ++ "." ++ reverse s) $ 
		      splitAt 3 $ reverse $ 
			      show (len_s1 `mod` space_latex_width)-}


latex_io :: TextDetails -> IO () -> IO ()
latex_io (Chr c)   io  = putChar c >> io
latex_io (Str s) io 
    | null s        = io
    | all isSpace s = putStr (sub_space s) >> io
    | otherwise      = putStr s >> io
latex_io (PStr s) io = putStr s >> io



-- functions for producing IO printable Strings
renderLatex,renderText,renderLatexVerb :: Maybe Int -> Doc -> String

renderLatex mi d = fullRender (mode           latexStyle')
		              (lineLength     latexStyle')
			      (ribbonsPerLine latexStyle')
			      latex_txt
			      ""
			      d'
    where d' = ptext "\\begin{hetcasl}" $+$ d $+$ ptext "\\end{hetcasl}"
	  latexStyle' = latexStyle {lineLength = 
				     (case mi of
				      Nothing -> lineLength latexStyle
				      Just l  -> l) }

-- this lacks some environment starting and closing LaTeX commands

renderLatexVerb mi d = renderStyle textStyle' d'
    where d' = text "\\begin{verbatim}" $+$ d $+$ text "\\end{verbatim}"
	  textStyle' = textStyle {lineLength = 
				     (case mi of
				      Nothing -> lineLength textStyle
				      Just l  -> l) }

renderText mi d = renderStyle textStyle' d
    where textStyle' = textStyle {lineLength = 
				     (case mi of
				      Nothing -> lineLength textStyle
				      Just l  -> l) }

-- moved instance from Id.hs (to avoid cyclic imports via GlobalAnnotations)
instance PrettyPrint Token where
    printText0 _ = ptext . tokStr

    printLatex0 _ = hc_sty_id . escape_latex . tokStr 

instance PrettyPrint Id where
    printText0 _ i = text (showId i "")
    printLatex0 _ i = hc_sty_id $ escape_latex $ showId i ""

-- some useful instances ---------------------------------------------


instance PrettyPrint String where
    printText0  _ = ptext 
    printLatex0  _ = error "use a 'casl_*_text' function directly" 



