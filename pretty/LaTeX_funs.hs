
{- |
   > HetCATS/pretty/LaTeX_funs.hs
   > $Id$
   > Author: Klaus Lüttich
   > Year: 2002

   Functions to calculate the length of a given word as it would be
   printed with LaTeX according to one of four categories of words
   useful for CASL:

   * keywords -- all the things that were printed in boldface

   * structid -- all the names used in the structured context of CASL

   * annotation -- all the comments and annotations of CASL in a smaller font

   * axiom -- identifiers in math mode for CASL Basic specs

   TODO:
     - itCorrection should be based on a map of character pairs to
       corrections and not on one fixed value for every pair 

-}


module LaTeX_funs (
		   space_latex_width,

		   calc_line_length,
		   -- calc_word_width,
		   -- Word_type(..),
		   keyword_width, structid_width, axiom_width, 
		   annotation_width, annotationbf_width, comment_width,
		   normal_width,

		   escape_latex,
		   (<\+>),
		   (<~>),
		   latex_macro,
                   comma_latex,
		   semi_latex,
		   colon_latex,
		   equals_latex,
		   space_latex,
                   
                   braces_latex, 
		   parens_latex, 
		   brackets_latex,

                   nest_latex,
		   hang_latex,
		   sep_latex,
		   fsep_latex,
		   
		   initial_keyword_latex,

		   casl_keyword_latex, 
		   casl_annotation_latex, 
		   casl_annotationbf_latex, 
		   casl_axiom_latex,
		   casl_comment_latex, 
		   casl_structid_latex,
		   casl_normal_latex,

                   hc_sty_keyword,
		   hc_sty_small_keyword,
		   hc_sty_plain_keyword,
		   hc_sty_hetcasl_keyword,

                   hc_sty_comment,
		   hc_sty_annotation,

                   hc_sty_axiom,
                   hc_sty_structid,
                   hc_sty_id
) where

import FiniteMap
import Char

-- for the debug hack
import IOExts

import LaTeX_maps
import Pretty

infixl 6 <\+>, <~>

space_latex_width :: Int
space_latex_width = normal_width " "

{- functions for calculating an interger value according to a given
   length in LaTeX units

   Units per mm found in: Karsten Günther, "Einführung in LaTeX2e" (p.376)

-}

calc_line_length :: String -> Int
calc_line_length s = 
    let (r_unit,r_number) = 
	    (\(x,y) -> (reverse x,reverse y)) $ span isAlpha $ reverse s
	unit = case r_unit of
	       "mm" -> 1
	       "cm" -> 10
	       "pt" -> 0.351
	       "in" -> 25.4
	       u    -> error ( "unknown or unsupported LaTeX unit: " ++ u )
	len :: Double
	len = read $ map (\c -> case c of ',' -> '.';_ -> c) r_number
    in truncate (len * unit * 1000)

-- a hack to have some debug prints
condTrace :: String -> a -> a
condTrace s v = if debugFlag then trace s v else v
    where debugFlag = True

{- functions to calculate a word-width in integer with a given word
   type or purpose

-}

data Word_type = Keyword | StructId | Normal
	       | Comment | Annotation | AnnotationBold
	       | Axiom 
		 deriving (Show,Eq)

calc_word_width :: Word_type -> String -> Int
calc_word_width wt s = 
    case lookupFM wFM s of
    Just l  -> l
    Nothing -> sum_char_width_deb (  showString "In map \""
				   . showsPrec 0 wt 
				   . showString "\" \'") wFM s - correction
    where wFM = case wt of
		 Keyword        -> keyword_map
		 StructId       -> structid_map
		 Comment        -> comment_map
		 Annotation     -> annotation_map
		 AnnotationBold -> annotationbf_map
		 Axiom          -> axiom_map
		 Normal         -> normal_map
	  correction = case wt of 
		       Axiom -> itCorrection s
		       _     -> 0

itCorrection :: String -> Int
itCorrection [] = 0
itCorrection s
    | length s < 2 = 0
    | otherwise    = itCorrection' 0 s
    where itCorrection' :: Int -> String -> Int
	  itCorrection' _ [] = error "itCorrection' applied to empty List"
	  itCorrection' r ys@(y1:[y2]) 
	      | not (isAlphaNum y1) = r 
	      | not (isAlphaNum y2) = r 
	      | otherwise           = r + lookupCorrection ys

	  itCorrection' r (y1:(ys@(y2:_)))
	      | not (isAlphaNum y1) = itCorrection' r ys
	      | otherwise           =
		  itCorrection' 
		        (r + lookupCorrection (y1:y2:[])) 
			ys
	  itCorrection' _ _ = error ("itCorrection' doesn't work with " ++ s)
	  lookupCorrection _pc = def_cor
	  -- lookupWithDefaultFM correction_map def_cor pc
	  -- TODO: Build a nice correction map
          def_cor = 610
 

sum_char_width_deb :: (String -> String) -- only used for an hackie debug thing
		   -> FiniteMap String Int -> String -> Int
sum_char_width_deb pref_fun cFM s = sum_char_width' s 0
    where sum_char_width' []  r = r
	  sum_char_width' [c] r 
	      | c == ' '  = r + lookupWithDefault_cFM "~"
	      | otherwise = r + lookupWithDefault_cFM (c:[])
	  sum_char_width' (c1:rest@(c2:cs)) r 
	      | isLigature (c1:c2:[]) = case lookupFM cFM (c1:c2:[]) of
					Just l  -> sum_char_width' cs (r+l)
					Nothing -> sum_char_width' rest nl
	      | (c1:c2:[]) == "\\ " =  
		  sum_char_width' cs (r + lookupWithDefault_cFM "~")
	      | c1 == ' ' =
		  sum_char_width' rest (r + lookupWithDefault_cFM "~")
	      | otherwise = sum_char_width' rest nl 
	      where nl = r + lookupWithDefault_cFM (c1:[])
	  lookupWithDefault_cFM s' = case lookupFM cFM s' of
				     Nothing -> condTrace 
					           ((pref_fun
						     . showString s' 
						     . showString "\' of \"" 
						     . showString s)
						    "\" not found!")
						   2200
				     Just w  -> w    

isLigature :: String -> Bool
isLigature s 
    | (length s) /= 2 = False
    | otherwise = lookupWithDefaultFM ligatures False s

keyword_width, structid_width, axiom_width, annotationbf_width,
  annotation_width, comment_width, normal_width
      :: String -> Int
annotation_width   = calc_word_width Annotation
annotationbf_width = calc_word_width AnnotationBold
keyword_width      = calc_word_width Keyword
structid_width     = calc_word_width StructId
axiom_width        = calc_word_width Axiom
comment_width      = calc_word_width Comment
normal_width       = calc_word_width Normal

-- |
-- LaTeX version of <+> with enough space counted.  It's choosen the
-- space between keywords which is nearly the average width of a
-- space.
(<\+>) :: Doc -> Doc -> Doc
-- TODO: did not work correctly !!!
d1 <\+> d2 = if isEmpty d1 
	     then (if isEmpty d2 
		   then empty
		   else d2)
	     else (if isEmpty d2
		   then d1
		   else 
		   d1 <> casl_normal_latex " " <> d2)

(<~>) :: Doc -> Doc -> Doc
d1 <~> d2 = d1 <> casl_normal_latex "~" <> d2

-- |
-- latex_macro creates a document ('Doc') containing String 
-- that has a zero width.
-- So it can be used for LaTeX-macros not needing any space, i.e. 
-- @\textit{@ or @}@
latex_macro :: String -> Doc
latex_macro = sp_text 0 
{- an alternative implementation of 
   latex_text with bad counts for letters etc. :

   case sp_length s 0 of {sl -> sp_text sl s}
    where
    sp_length :: String -> Int -> Int 
    sp_length ""     a   = a
    sp_length (x:xs) a 
	| x == '\\' = let (c,rest) = spanLaMacro xs 
		      in sp_length rest (a+c)
	| x == '{'  = sp_length xs a 
	| x == '}'  = sp_length xs a 
	| otherwise = sp_length xs (a+1) 
	where spanLaMacro :: String -> (Int, String)
	      spanLaMacro "" = (1,"") -- lambda
	      spanLaMacro (x:xs) 
		  | x == ' '  = (1,xs) -- an explicit space 
		  | x == '{'  = (1,xs)
		  | x == '}'  = (1,xs)
		  | x == '_'  = (1,xs)  
		  | isAlpha x = let (makro,rest) = 
					span isAlpha xs
				in (0,rest) 
		  | otherwise = (0,x:xs) 
                                 -- error $ "spanLaMacro: strange " ++ 
				 --    take 5 (x:xs)

-}

comma_latex, semi_latex, space_latex,equals_latex,colon_latex :: Doc 
comma_latex  = let s = "," in sp_text (normal_width s) s
semi_latex   = let s = ";" in sp_text (normal_width s) s
colon_latex  = let s = ":" in sp_text (normal_width s) s
space_latex  = let s = " " in sp_text (normal_width s) s
equals_latex = hc_sty_axiom "="

braces_latex, parens_latex, brackets_latex :: Doc -> Doc
braces_latex d   = casl_normal_latex "\\{"<>d<>casl_normal_latex "\\}"
parens_latex d   = casl_normal_latex "("<>d<>casl_normal_latex ")"
brackets_latex d = casl_normal_latex "["<>d<>casl_normal_latex "]"

-- nest and hang that do the obvious thing except that they use
-- multiple spaces for indentation
nest_latex :: Int -> Doc -> Doc
nest_latex k = nest (k * space_latex_width)
     
hang_latex :: Doc -> Int -> Doc -> Doc
hang_latex d1 n d2 = sep_latex [d1, nest_latex n d2]

sep_latex :: [Doc] -> Doc
sep_latex = cat . (cond_punctuate (casl_normal_latex " "))

fsep_latex :: [Doc] -> Doc
fsep_latex = fcat . (cond_punctuate (casl_normal_latex " "))

initial_keyword_latex :: String -> String -> Doc
initial_keyword_latex fs kw =
    let fs_w = keyword_width fs
	kw_w = keyword_width kw
    in if kw_w <= fs_w  then
          sp_text fs_w kw
       else
          sp_text kw_w kw

casl_keyword_latex, casl_annotation_latex, casl_annotationbf_latex, 
       casl_axiom_latex,
       casl_comment_latex, casl_structid_latex,
       casl_normal_latex :: String -> Doc
casl_keyword_latex s      = sp_text (keyword_width s)    s
casl_annotation_latex s   = sp_text (annotation_width s) s
casl_annotationbf_latex s = sp_text (annotationbf_width s) s
casl_comment_latex s      = sp_text (comment_width s)    s
casl_structid_latex s     = sp_text (structid_width s)   s
casl_axiom_latex s        = sp_text (axiom_width s)      s
casl_normal_latex s       = sp_text (normal_width s)     s
hc_sty_keyword :: Maybe String -> String -> Doc
hc_sty_keyword mfkw kw = 
    latex_macro "\\KW"<>fkw_doc<>latex_macro "{"<>kw_doc<> latex_macro "}"
    where (fkw_doc,kw_doc) = 
	      case mfkw of
	      Just fkw -> (latex_macro "["<>latex_macro fkw<>latex_macro "]",
			   initial_keyword_latex fkw kw)
	      Nothing  -> (empty,casl_keyword_latex kw)
	 
hc_sty_plain_keyword :: String -> Doc
hc_sty_plain_keyword = hc_sty_keyword Nothing

hc_sty_hetcasl_keyword :: String -> Doc
hc_sty_hetcasl_keyword = hc_sty_keyword (Just "view")

hc_sty_small_keyword :: String -> Doc
hc_sty_small_keyword kw = 
    latex_macro "\\KW{" <> casl_annotationbf_latex kw <> latex_macro "}"

hc_sty_comment, hc_sty_annotation :: Doc -> Doc
hc_sty_comment cm = latex_macro "{\\small{}" <> cm <> latex_macro "}"
hc_sty_annotation = hc_sty_comment

hc_sty_axiom, hc_sty_structid, hc_sty_id :: String -> Doc
hc_sty_structid sid = latex_macro "\\SId{"<>sid_doc<>latex_macro "}"
    where sid_doc = casl_structid_latex (escape_latex sid)
hc_sty_id i        = latex_macro "\\Id{"<>id_doc<>latex_macro "}"
    where id_doc = casl_axiom_latex i
hc_sty_axiom ax = latex_macro "\\Ax{"<>ax_doc<>latex_macro "}"
    where ax_doc = casl_axiom_latex ax

cond_punctuate :: Doc -> [Doc] -> [Doc]
cond_punctuate _p []     = []
cond_punctuate p (doc:docs) = go doc docs
    where go d []     = [d]
          go d (e:es) = cond_predicate : go e es
	      where cond_predicate = if isEmpty d then d else d<>p

-- moved from PPUtils (used for String instance of PrettyPrint and
-- various other functions that print Strings with special stuff
-- inside)
escape_latex :: String -> String
escape_latex "" = ""
escape_latex (x:xs) 
    | x `elem` "_%{}" = '\\':x:(escape_latex xs)
    | x `elem` "~^"   = '\\':x:("{}"++escape_latex xs)
    | otherwise       =      x:(escape_latex xs)
