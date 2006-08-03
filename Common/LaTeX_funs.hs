{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
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
-}
{-
   TODO:
     - itCorrection should be based on a map of character pairs to
       corrections and not on one fixed value for every pair
-}

module Common.LaTeX_funs
    ( calc_line_length,
     pt_length,
     keyword_width, axiom_width,
     normal_width,

     hspace_latex,
     (<\+>),
     (<~>),
     latex_macro,
     comma_latex,
     semi_latex,
     space_latex,

     parens_latex,
     brackets_latex,
     quotes_latex,

     sep_latex,
     fsep_latex,

     casl_keyword_latex,
     casl_annotation_latex,
     casl_annotationbf_latex,
     casl_axiom_latex,
     casl_comment_latex,
     casl_structid_latex,
     casl_normal_latex,

     hc_sty_small_keyword,
     hc_sty_plain_keyword,
     hc_sty_hetcasl_keyword,
     hc_sty_casl_keyword,

     hc_sty_comment,
     hc_sty_annotation,

     hc_sty_axiom,
     hc_sty_structid,
     hc_sty_structid_indexed,
     hc_sty_id,

     flushright
    , equals_latex
    , less_latex
    , colon_latex
    , dot_latex
    , bullet_latex
    , mapsto_latex
    , rightArrow
    , pfun_latex
    , cfun_latex
    , pcfun_latex
    , exequal_latex
    , forall_latex
    , exists_latex
    , unique_latex

    , startTab, endTab, setTab
    , setTabWSp
    , startAnno
    , endAnno
    , escapeLatex
    ) where

import qualified Common.Lib.Map as Map
import Data.Char
import Data.List (isPrefixOf)
import Numeric

import Common.LaTeX_maps
import Common.Lib.Pretty as Pretty
import Text.ParserCombinators.Parsec as Parsec

infixl 6 <\+>, <~>

-- |
-- a constant String for starting a LaTeX indentation with tab stop
startTab :: String
startTab = "\\@begT@"

-- |
-- a constant String for releasing a LaTeX indentation with tab stop
endTab :: String
endTab = "\\@endT@"

-- |
-- a constant String to set a tab stop and enable it
setTab :: String
setTab = "\\="

-- | a constant String indicating the start of a space based indentation
setTabWSp :: String
setTabWSp = "\\@setTS@{"

{- functions for calculating an integer value according to a given
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

data Word_type =
    Keyword | StructId | Normal | Comment | Annotation | AnnotationBold | Axiom
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
    | length s < 2 || head s == '\\' = 0
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
                            Nothing -> if c1 == '\\' then
                                        sum_char_width'
                                        (dropWhile isAlpha rest)
                                         $ r + lookupWithDefault_cFM "~"
                                        else sum_char_width' rest nl
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
comment_width      = calc_word_width Comment
normal_width       = calc_word_width Normal
axiom_width        = sum . map (calc_word_width Axiom) . parseAxiomString

-- |
-- LaTeX version of '<+>' with enough space counted.  It's choosen the
-- space between keywords which is nearly the average width of a
-- space.
(<\+>) :: Doc -> Doc -> Doc
-- TODO: did not work correctly !!!
d1 <\+> d2 = if isEmpty d1 then d2 else
                 if isEmpty d2 then d1 else d1 <> space_latex <> d2

(<~>) :: Doc -> Doc -> Doc
d1 <~> d2 = d1 <> casl_normal_latex "~" <> d2

-- |
-- latex_macro creates a document ('Doc') containing String
-- that has a zero width.
-- So it can be used for LaTeX-macros not needing any space, i.e.
-- @\textit{@ or @}@
latex_macro :: String -> Doc
latex_macro = sp_text 0

comma_latex, semi_latex, space_latex :: Doc
comma_latex  = casl_normal_latex ","
semi_latex   = casl_normal_latex ";"
space_latex  = casl_normal_latex " "

parens_latex, brackets_latex, quotes_latex :: Doc -> Doc
parens_latex d   = casl_normal_latex "("<>d<>casl_normal_latex ")"
brackets_latex d = casl_normal_latex "["<>d<>casl_normal_latex "]"
quotes_latex d = q <> d <> q
    where q = casl_normal_latex "{\\tt{}\\textquotedblright}"

sep_latex :: [Doc] -> Doc
sep_latex = cat . cond_punctuate space_latex

fsep_latex :: [Doc] -> Doc
fsep_latex = fcat . cond_punctuate space_latex

casl_keyword_latex, casl_annotation_latex, casl_annotationbf_latex,
       casl_axiom_latex,
       casl_comment_latex, casl_structid_latex,
       casl_normal_latex :: String -> Doc
casl_annotationbf_latex s = sp_text (annotationbf_width s) s
casl_annotation_latex s   = sp_text (annotation_width s) s
casl_structid_latex s     = sp_text (structid_width s) s
casl_comment_latex s      = sp_text (comment_width s) s
casl_keyword_latex s      = sp_text (keyword_width s) s
casl_normal_latex s       = sp_text (normal_width s) s
casl_axiom_latex s        = sp_text (axiom_width s) s

-- | form, spec, view, then
hc_sty_hetcasl_keyword :: String -> Doc
hc_sty_hetcasl_keyword str =
    sp_text (keyword_width "view") $ "\\" ++ map toUpper str

-- | sort, op, pred, type and its plurals
hc_sty_casl_keyword :: String -> Doc
hc_sty_casl_keyword str =
    sp_text (keyword_width "preds") $ "\\" ++ map toUpper str

hc_sty_plain_keyword :: String -> Doc
hc_sty_plain_keyword kw =
    latex_macro "\\KW{" <> casl_keyword_latex (escapeUnderline kw)
                    <> latex_macro "}"

hc_sty_small_keyword :: String -> Doc
hc_sty_small_keyword kw =
    latex_macro "\\KW{" <> casl_annotationbf_latex (escapeUnderline kw)
                    <> latex_macro "}"

hc_sty_comment, hc_sty_annotation :: Doc -> Doc
hc_sty_comment cm = latex_macro startAnno <> cm <> latex_macro endAnno
hc_sty_annotation = hc_sty_comment

hc_sty_axiom, hc_sty_structid, hc_sty_id,hc_sty_structid_indexed
    :: String -> Doc
hc_sty_structid sid = latex_macro "\\SId{"<>sid_doc<>latex_macro "}"
    where sid_doc = casl_structid_latex (escapeUnderline sid)
hc_sty_structid_indexed sid =
    latex_macro "\\SIdIndex{"<>sid_doc<>latex_macro "}"
    where sid_doc = casl_structid_latex (escapeUnderline sid)
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

-- | flush argument doc to the right
flushright :: Doc -> Doc
flushright d = latex_macro "\\`" <> d

-- |
-- makes a \hspace*{String} as Doc with appropiate size
hspace_latex :: String -> Doc
hspace_latex str = sp_text (calc_line_length str) ("\\hspace*{"++str++"}")

-- |
-- a constant String for the start of annotations
startAnno :: String
startAnno = "{\\small{}"

-- |
-- a constant string ending an annotation
endAnno :: String
endAnno = "%@%small@}"

escapeUnderline :: String -> String
escapeUnderline = concatMap ( \ c -> if c == '_' then "\\_" else [c])

escapeLatex :: Bool -> String -> String
escapeLatex addAx = concatMap ( \ c ->
     if elem c "_%$&{}#" then
         if addAx then "\\Ax{\\" ++ c : "}"
         else '\\' : [c]
     else if addAx && elem c "<|>=-!()[]?:;,./*+@" then "\\Ax{" ++ c : "}"
     else Map.findWithDefault [c] c escapeMap)

equals_latex, less_latex, colon_latex, dot_latex,
    bullet_latex, mapsto_latex, rightArrow, pfun_latex, cfun_latex,
    pcfun_latex, exequal_latex :: Doc
equals_latex = hc_sty_axiom "="
less_latex   = hc_sty_axiom "<"
colon_latex  = casl_normal_latex ":"
dot_latex    = casl_normal_latex "."
bullet_latex = hc_sty_axiom "\\bullet"
mapsto_latex = hc_sty_axiom "\\mapsto"
rightArrow   = hc_sty_axiom "\\rightarrow"
pfun_latex   = hc_sty_axiom "\\rightarrow?"
cfun_latex   = hc_sty_axiom "\\stackrel{c}{\\rightarrow}"
pcfun_latex  = hc_sty_axiom "\\stackrel{c}{\\rightarrow}?"
exequal_latex = sp_text (axiom_width "=") "\\Ax{\\stackrel{e}{=}}"

forall_latex, exists_latex, unique_latex :: Doc
forall_latex = hc_sty_axiom "\\forall"
exists_latex = hc_sty_axiom "\\exists"
unique_latex = hc_sty_axiom "\\exists!"

parseAxiomString :: String -> [String]
parseAxiomString s = case parse axiomString "" s of
    Left _ -> [s]
    Right l -> l

axiomString :: CharParser st [String]
axiomString = do
  l <- many parseAtom
  eof
  return $ concat l

parseAtom :: CharParser st [String]
parseAtom = do
    try (string "\\Ax{") <|> try (string "\\Id{") <|> string "{"
    l <- many parseAtom
    Parsec.char '}'
    return (concat l)
 <|> do
    b <- Parsec.char '\\'
    s <- fmap (: []) (satisfy (\ c -> isSpace c
                                      || elem c "_~^|\'\",;:.`\\{}[]%$&#()"))
         <|> many1 (satisfy isAlpha)
    return [b : s]
 <|> do
    s <- many1 (satisfy isAlpha)
    return [s]
 <|> do
    c <- satisfy (/= '}')
    return [[c]]

-- | a character map for special latex characters
escapeMap :: Map.Map Char String
escapeMap = Map.fromList
 [('\\' , "\\Ax{\\setminus}"),
  ('^' , "\\Ax{\\hat{\\ }}"),
  ('\"' , "\'\'"),
  ('~' , "\\Ax{\\sim}"),
  ('\160', "\\ "),
  ('¢' , "\\Id{\\textcent}"),
  ('¤' , "\\Id{\\textcurrency}"),
  ('¥' , "\\Id{\\textyen}"),
  ('¦' , "\\Id{\\textbrokenbar}"),
  ('ª' , "\\Id{\\textordfeminine}"),
  ('«' , "\\Id{\\guillemotleft}"),
  ('¬' , "\\Ax{\\neg}"),
  ('­' , "-"),
  ('®' , "\\Id{\\textregistered}"),
  ('\175', "\\Ax{\\bar{\\ }}"),
  ('°' , "\\Id{\\textdegree}"),
  ('±' , "\\Ax{\\pm}"),
  ('²' , "\\Ax{^2}"),
  ('³' , "\\Ax{^3}"),
  ('´' , "\\Ax{\\acute{\\ }}"),
  ('µ' , "\\Ax{\\mu}"),
  ('¹' , "\\Ax{^1}"),
  ('º' , "\\Id{\\textordmasculine}"),
  ('»' , "\\Id{\\guillemotright}"),
  ('À' , "\\Ax{\\grave{A}}"),
  ('Á' , "\\Ax{\\acute{A}}"),
  ('È' , "\\Ax{\\grave{E}}"),
  ('É' , "\\Ax{\\acute{E}}"),
  ('Ì' , "\\Ax{\\grave{I}}"),
  ('Í' , "\\Ax{\\acute{I}}"),
  ('Ð' , "\\Id{\\DH}"),
  ('Ò' , "\\Ax{\\grave{O}}"),
  ('Ó' , "\\Ax{\\acute{O}}"),
  ('×' , "\\Ax{\\times}"),
  ('Ù' , "\\Ax{\\grave{U}}"),
  ('Ú' , "\\Ax{\\acute{U}}"),
  ('Ý' , "\\Ax{\\acute{Y}}"),
  ('Þ' , "\\Id{\\TH}"),
  ('à' , "\\Ax{\\grave{a}}"),
  ('á' , "\\Ax{\\acute{a}}"),
  ('è' , "\\Ax{\\grave{e}}"),
  ('é' , "\\Ax{\\acute{e}}"),
  ('ì' , "\\Ax{\\grave{\\Id{\\i}}}"),
  ('í' , "\\Ax{\\acute{\\Id{\\i}}}"),
  ('ð' , "\\Id{\\dh}"),
  ('ò' , "\\Ax{\\grave{o}}"),
  ('ó' , "\\Ax{\\acute{o}}"),
  ('÷' , "\\Ax{\\div}"),
  ('ù' , "\\Ax{\\grave{u}}"),
  ('ú' , "\\Ax{\\acute{u}}"),
  ('ý' , "\\Ax{\\acute{y}}"),
  ('þ' , "\\Id{\\th}")]

{- acute and grave characters don't work in a tabbing environment
   \textcent upto textbrokenbar requires \usepackage{textcomp}
    whereas \guillemot, eth, and thorn  \usepackage[T1]{fontenc}
-}
