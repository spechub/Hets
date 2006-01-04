
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

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


module Common.LaTeX_funs (-- module Common.LaTeX_funs,
                   space_latex_width,

                   calc_line_length,
                   pt_length,
                   -- calc_word_width,
                   -- Word_type(..),
                   keyword_width, structid_width, axiom_width, 
                   annotation_width, annotationbf_width, comment_width,
                   normal_width,

                   escape_latex,
                   escape_comment_latex,
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
                   quotes_latex,

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
                   hc_sty_structid_indexed,
                   hc_sty_id,

                   startAnno,
                   endAnno
) where

import qualified Common.Lib.Map as Map
import Data.Char
import Data.List (isPrefixOf)
import Numeric

import Common.LaTeX_maps
import Common.Lib.Pretty

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

pt_length :: Int -> String
pt_length i = showFFloat (Just 3) pt "pt"
    where pt :: Float
          pt = fromRational (toRational i /351) 

{- functions to calculate a word-width in integer with a given word
   type or purpose

-}

data Word_type = Keyword | StructId | Normal
               | Comment | Annotation | AnnotationBold
               | Axiom 
                 deriving (Show,Eq)

calc_word_width :: Word_type -> String -> Int
calc_word_width wt s = 
    case Map.lookup s wFM of
    Just l  -> l
    Nothing -> sum_char_width_deb (  showString "In map \""
                                   . showsPrec 0 wt 
                                   . showString "\" \'") wFM k_wFM s 
                 - correction
    where (wFM,k_wFM) = case wt of
                        Keyword        -> (keyword_map,key_keyword_map)
                        StructId       -> (structid_map,key_structid_map)
                        Comment        -> (comment_map,key_comment_map)
                        Annotation     -> (annotation_map,key_annotation_map)
                        AnnotationBold -> (annotationbf_map,
                                           key_annotationbf_map)
                        Axiom          -> (axiom_map,key_axiom_map)
                        Normal         -> (normal_map,key_normal_map)
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
          lookupCorrection str = Map.findWithDefault def_cor str 
                                 italiccorrection_map 
          -- lookupWithDefaultFM correction_map def_cor pc
          -- TODO: Build a nice correction map
          def_cor = 610
 

sum_char_width_deb :: (String -> String) -- only used for an hackie debug thing
                   -> Map.Map String Int 
                   -> Map.Map Char [String]  -> String -> Int
sum_char_width_deb _pref_fun cFM key_cFM s = sum_char_width' s 0
    where sum_char_width' []  r = r
          sum_char_width' [c] r 
              | c == ' '  = r + lookupWithDefault_cFM "~"
              | otherwise = r + lookupWithDefault_cFM (c:[])
          sum_char_width' full@(c1:rest@(c2:cs)) r 
              | isLigature (c1:c2:[]) = case Map.lookup (c1:c2:[]) cFM of
                                        Just l  -> sum_char_width' cs (r+l)
                                        Nothing -> sum_char_width' rest nl
              | (c1:c2:[]) == "\\ " =  
                  sum_char_width' cs (r + lookupWithDefault_cFM "~")         
              | c1 == ' ' =
                  sum_char_width' rest (r + lookupWithDefault_cFM "~")
              | otherwise = case prefixIsKey full key_cFM of
                            Just key -> sum_char_width' 
                                        (drop (length key) full) 
                                        $ r + (cFM Map.! key)
                            Nothing -> sum_char_width' rest nl 
              where nl = r + lookupWithDefault_cFM (c1:[])
          lookupWithDefault_cFM s' = case Map.lookup s' cFM of
                                     Nothing -> {- trace 
                                                   ((pref_fun
                                                     . showString s' 
                                                     . showString "\' of \"" 
                                                     . showString s)
                                                    "\" not found!") -}
                                                   2200
                                     Just w  -> w    

prefixIsKey :: String -> Map.Map Char [String] -> Maybe String
prefixIsKey [] _ = Nothing
prefixIsKey ls@(c:_) key_cFM = case filter (flip isPrefixOf ls) 
        $ Map.findWithDefault [] c key_cFM of 
    [] -> Nothing
    s : _ -> Just s

isLigature :: String -> Bool
isLigature s 
    | (length s) /= 2 = False
    | otherwise = Map.findWithDefault False s ligatures

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
-- LaTeX version of '<+>' with enough space counted.  It's choosen the
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

comma_latex, semi_latex, space_latex,equals_latex,colon_latex :: Doc 
comma_latex  = let s = "," in sp_text (normal_width s) s
semi_latex   = let s = ";" in sp_text (normal_width s) s
colon_latex  = let s = ":" in sp_text (normal_width s) s
space_latex  = let s = " " in sp_text (normal_width s) s
equals_latex = hc_sty_axiom "="

braces_latex, parens_latex, brackets_latex, quotes_latex :: Doc -> Doc
braces_latex d   = casl_normal_latex "\\{"<>d<>casl_normal_latex "\\}"
parens_latex d   = casl_normal_latex "("<>d<>casl_normal_latex ")"
brackets_latex d = casl_normal_latex "["<>d<>casl_normal_latex "]"
quotes_latex d = q <> d <> q
    where q = casl_normal_latex "{\\tt{}\\textquotedblright}"

-- nest and hang that do the obvious thing except that they use
-- multiple spaces for indentation and set tabs with spaces
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
casl_annotation_latex s   = let s' = conv s 
                            in sp_text (annotation_width s) s'
    where conv [] = []
          conv (x:xs) 
              | x == '~' = "\\sim{}"++conv xs
              | otherwise = x:conv xs

casl_annotationbf_latex s = sp_text (annotationbf_width s) s
casl_comment_latex s      = sp_text (comment_width s)    s
casl_structid_latex s     = sp_text (structid_width s)   s
casl_axiom_latex s        = let s' = conv s 
                            in sp_text (axiom_width s') s'
    where conv [] = []
          conv (x:xs) 
              | x == '~'  = "\\sim{}"++conv xs
              | otherwise = x:conv xs

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
hc_sty_plain_keyword str = 
    case str of
    "library" -> sp_t "\\LIBRARY"
    "to" -> sp_t "\\TO"
    "get" -> sp_t "\\GET"
    "version" -> sp_t "\\VERSION"
    "end" -> sp_t "\\END"
    "and" -> sp_t "\\AND"
    "arch spec" -> sp_t "\\ARCHSPEC"
    "unit spec" -> sp_t "\\UNITSPEC"
    "free" -> sp_t "\\FREE"
    "local" -> sp_t "\\LOCAL"
    "within" -> sp_t "\\WITHIN"
    "closed" -> sp_t "\\CLOSED"
    "with" -> sp_t "\\WITH"
    "logic" -> sp_t "\\LOGIC"
    "hide" -> sp_t "\\HIDE"
    "reveal" -> sp_t "\\REVEAL"
    "given" -> sp_t "\\GIVEN"
    "fit" -> sp_t "\\FIT"
    "view" -> sp_t "\\VIEW"
    "generated" -> sp_t "\\GENERATED"
    "vars" -> sp_t "\\VARS"
    "sort" -> sp_t "\\SORT[KW]"
    "sorts" -> sp_t "\\SORTS[KW]"
    "op" -> sp_t "\\OP[KW]"
    "ops" -> sp_t "\\OPS[KW]"
    "type" -> sp_t "\\TYPE[KW]"
    "types" -> sp_t "\\TYPES[KW]"
    "pred" -> sp_t "\\PRED[KW]"
    "preds" -> sp_t "\\PREDS[KW]"
    str' -> hc_sty_keyword Nothing str'
    where sp_t s = sp_text (keyword_width "") s
        
-- Heng Todo: case Anweisung fortführen und für hc_sty_plain_keyword
hc_sty_hetcasl_keyword :: String -> Doc
hc_sty_hetcasl_keyword str = 
    case str of
    "then" -> sp_t "\\THEN"
    "spec" -> sp_t "\\SPEC"
    "view" -> sp_t "\\VIEW"
    "from" -> sp_t "\\FROM"
    str'   -> hc_sty_keyword (Just "view") str'
    where sp_t s = sp_text (keyword_width "view") s
    
hc_sty_small_keyword :: String -> Doc
hc_sty_small_keyword kw = 
    latex_macro "\\KW{" <> casl_annotationbf_latex kw <> latex_macro "}"

hc_sty_comment, hc_sty_annotation :: Doc -> Doc
hc_sty_comment cm = latex_macro startAnno <> cm <> latex_macro endAnno
hc_sty_annotation = hc_sty_comment

hc_sty_axiom, hc_sty_structid, hc_sty_id,hc_sty_structid_indexed 
    :: String -> Doc
hc_sty_structid sid = latex_macro "\\SId{"<>sid_doc<>latex_macro "}"
    where sid_doc = casl_structid_latex (escape_latex sid)
hc_sty_structid_indexed sid = 
    latex_macro "\\SIdIndex{"<>sid_doc<>latex_macro "}"
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

-- |
-- a constant String for the start of annotations
startAnno :: String
startAnno = "{\\small{}"

-- |
-- a constant string ending an annotation
endAnno :: String
endAnno = "%@%small@}"

-- moved from PPUtils (used for String instance of PrettyPrint and
-- various other functions that print Strings with special stuff
-- inside)
escape_latex :: String -> String
escape_latex "" = ""
escape_latex (x:xs) 
    | x == '\\' = "\\textbackslash" ++ '{':'}':escape_latex xs
    | x == '"' = -- something to prevent german.sty from interpreting '"'
             case xs of
             []  -> default_quotes []
             y:ys | isAlphaNum y -> '`':'`':y:escape_latex ys
                  | isSpace    y -> default_quotes (y:escape_latex ys)
                  | otherwise    -> default_quotes (escape_latex xs) 
    | x `elem` "_%$&{}#" = '\\':x:escape_latex xs
    | x == '~' = "\\Ax{\\sim}" ++escape_latex xs
    | x == '^'   = '\\':x:("{}"++escape_latex xs)
    | otherwise       =      x:escape_latex xs
    where default_quotes = ('\'':) . ('\'':)

escape_comment_latex :: String -> String
escape_comment_latex s
    |  or $ map (`elem` s) "<>" = ecl s'
    | otherwise = s'
    where s' = escape_latex s
          ecl "" = ""
          ecl (x:xs)
              | x == '<' 
                || x == '>' = "\\Ax{"++x:"}"++ecl xs
              | otherwise   = x: ecl xs
