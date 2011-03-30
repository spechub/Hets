{- |
Module      :  $Header$
Description :  auxiliary functions for LaTeX printing
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Auxiliary functions for LaTeX printing

Functions to calculate the length of a given word as it would be
   printed with LaTeX according to one of four categories of words
   useful for CASL:

   * keywords -- all the things that were printed in boldface

   * structid -- all the names used in the structured context of CASL

   * annotation -- all the comments and annotations of CASL in a smaller font

   * axiom -- identifiers in math mode for CASL Basic specs
-}

module Common.LaTeX_funs
    ( calc_line_length
    , axiom_width
    , latex_macro
    , flushright
    , casl_comment_latex
    , casl_normal_latex

    , hc_sty_small_keyword
    , hc_sty_plain_keyword
    , hc_sty_casl_keyword

    , hc_sty_axiom
    , hc_sty_structid
    , hc_sty_structid_indexed
    , hc_sty_id

    , startTab, endTab, setTab
    , setTabWSp
    , startAnno
    , endAnno
    , escapeSpecial
    , escapeLatex
    ) where

import qualified Data.Map as Map
import Data.Char
import Data.List (isPrefixOf)

import Common.LaTeX_maps
import Common.Lib.Pretty as Pretty
import Common.Parsec
import Text.ParserCombinators.Parsec as Parsec

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

   Units per mm found in: Karsten Guenther, "Einfuehrung in LaTeX2e" (p.376)
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
        len = read $ map (\ c -> case c of
                                   ',' -> '.'
                                   _ -> c) r_number
    in truncate (len * unit * 1000)

{- functions to calculate a word-width in integer with a given word
   type or purpose
-}

data Word_type =
    Keyword | StructId | Normal | Comment | Annotation | AnnotationBold | Axiom
    deriving (Show,Eq)

calc_word_width :: Word_type -> String -> Int
calc_word_width wt s = Map.findWithDefault
  (sum_char_width_deb (showString "In map \"" . shows wt . showString "\" \'")
   wFM k_wFM s - correction) s wFM
    where (wFM, k_wFM) = case wt of
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
          itCorrection' r ys@[y1, y2]
              | not (isAlphaNum y1) = r
              | not (isAlphaNum y2) = r
              | otherwise           = r + lookupCorrection ys

          itCorrection' r (y1 : ys@(y2 : _))
              | not (isAlphaNum y1) = itCorrection' r ys
              | otherwise           =
                  itCorrection'
                        (r + lookupCorrection [y1, y2])
                        ys
          itCorrection' _ _ = error ("itCorrection' doesn't work with " ++ s)
          lookupCorrection str = Map.findWithDefault def_cor str
                                 italiccorrection_map
          def_cor = 610

sum_char_width_deb :: (String -> String) -- only used for an hackie debug thing
                   -> Map.Map String Int
                   -> Map.Map Char [String]  -> String -> Int
sum_char_width_deb _pref_fun cFM key_cFM s = sum_char_width' s 0
    where sum_char_width' []  r = r
          sum_char_width' [c] r = r + case c of
              '}' -> 0
              '{' -> 0
              ' ' -> lookupWithDefault_cFM "~"
              _ -> lookupWithDefault_cFM [c]
          sum_char_width' full@(c1:rest@(c2:cs)) r
              | isLigature [c1, c2] = case Map.lookup [c1, c2] cFM of
                                        Just l  -> sum_char_width' cs (r+l)
                                        Nothing -> sum_char_width' rest nl
              | [c1, c2] == "\\ " =
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
              where nl = r + lookupWithDefault_cFM [c1]
          lookupWithDefault_cFM s' = Map.findWithDefault 2200 s' cFM
              -- 2200 may not be optimal


prefixIsKey :: String -> Map.Map Char [String] -> Maybe String
prefixIsKey [] _ = Nothing
prefixIsKey ls@(c:_) key_cFM = case filter (`isPrefixOf` ls)
        $ Map.findWithDefault [] c key_cFM of
    [] -> Nothing
    s : _ -> Just s

isLigature :: String -> Bool
isLigature s = case s of
  [_, _] -> Map.findWithDefault False s ligatures
  _ -> False

keyword_width, structid_width, axiom_width, annotationbf_width,
    comment_width, normal_width :: String -> Int
annotationbf_width = calc_word_width AnnotationBold
keyword_width      = calc_word_width Keyword
structid_width     = calc_word_width StructId
comment_width      = calc_word_width Comment
normal_width       = calc_word_width Normal
axiom_width        = sum . map (calc_word_width Axiom) . parseAxiomString

-- |
-- latex_macro creates a document ('Doc') containing String
-- that has a zero width.
-- So it can be used for LaTeX-macros not needing any space, i.e.
-- @\textit{@ or @}@
latex_macro :: String -> Doc
latex_macro = sp_text 0

casl_keyword_latex, casl_annotationbf_latex,
       casl_axiom_latex,
       casl_comment_latex, casl_structid_latex,
       casl_normal_latex :: String -> Doc
casl_annotationbf_latex s = sp_text (annotationbf_width s) s
casl_structid_latex s     = sp_text (structid_width s) s
casl_comment_latex s      = sp_text (comment_width s) s
casl_keyword_latex s      = sp_text (keyword_width s) s
casl_normal_latex s       = sp_text (normal_width s) s
casl_axiom_latex s        = sp_text (axiom_width s) s

-- | sort, op, pred, type and its plurals
hc_sty_casl_keyword :: String -> Doc
hc_sty_casl_keyword str =
    sp_text (keyword_width "preds") $ '\\' : map toUpper str

hc_sty_plain_keyword :: String -> Doc
hc_sty_plain_keyword kw =
    latex_macro "\\KW{" <> casl_keyword_latex (escapeSpecial kw)
                    <> latex_macro "}"

hc_sty_small_keyword :: String -> Doc
hc_sty_small_keyword kw =
    latex_macro "\\KW{" <> casl_annotationbf_latex (escapeSpecial kw)
                    <> latex_macro "}"

hc_sty_axiom, hc_sty_structid, hc_sty_id,hc_sty_structid_indexed
    :: String -> Doc
hc_sty_structid sid = latex_macro "\\SId{"<>sid_doc<>latex_macro "}"
    where sid_doc = casl_structid_latex (escapeSpecial sid)
hc_sty_structid_indexed sid =
    latex_macro "\\SIdIndex{"<>sid_doc<>latex_macro "}"
    where sid_doc = casl_structid_latex (escapeSpecial sid)
hc_sty_id i        = latex_macro "\\Id{"<>id_doc<>latex_macro "}"
    where id_doc = casl_axiom_latex i
hc_sty_axiom ax = latex_macro "\\Ax{"<>ax_doc<>latex_macro "}"
    where ax_doc = casl_axiom_latex ax

-- | flush argument doc to the right
flushright :: Doc -> Doc
flushright = (latex_macro "\\`" <>)

-- |
-- a constant String for the start of annotations
startAnno :: String
startAnno = "{\\small{}"

-- |
-- a constant string ending an annotation
endAnno :: String
endAnno = "%@%small@}"

escapeSpecial :: String -> String
escapeSpecial = concatMap $ \ c -> if  elem c "_%$&{}#" then '\\' : [c] else
  Map.findWithDefault [c] c escapeMap

escapeLatex :: String -> String
escapeLatex = concatMap $ \ c -> case () of
  ()
    | elem c "_%$&{}#" -> "\\Ax{\\" ++ c : "}"
    | elem c "<|>=-!()[]?:;,./*+@" -> "\\Ax{" ++ c : "}"
    | otherwise -> Map.findWithDefault [c] c escapeMap

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
    tryString "\\Ax{" <|> tryString "\\Id{" <|> string "{"
    l <- many parseAtom
    Parsec.char '}'
    return (concat l)
 <|> do
    b <- Parsec.char '\\'
    s <- fmap (: []) (satisfy (\ c -> isSpace c
                                      || elem c "_~^|\'\",;:.`\\{}[]%$&#()"))
         <|> many1 letter
    return [b : s]
 <|> do
    s <- many1 letter
    return [s]
 <|> do
    c <- satisfy (/= '}')
    return [[c]]

-- | a character map for special latex characters
escapeMap :: Map.Map Char String
escapeMap = Map.fromList
 [('\\',"\\Ax{\\setminus}"),
  ('^',"\\Ax{\\hat{\\ }}"),
  ('"',"''"),
  ('~',"\\Ax{\\sim}"),
  ('\160',"\\ "),
  ('\162',"\\Id{\\textcent}"),
  ('\164',"\\Id{\\textcurrency}"),
  ('\165',"\\Id{\\textyen}"),
  ('\166',"\\Id{\\textbrokenbar}"),
  ('\170',"\\Id{\\textordfeminine}"),
  ('\171',"\\Id{\\guillemotleft}"),
  ('\172',"\\Ax{\\neg}"),
  ('\173',"-"),
  ('\174',"\\Id{\\textregistered}"),
  ('\175',"\\Ax{\\bar{\\ }}"),
  ('\176',"\\Id{\\textdegree}"),
  ('\177',"\\Ax{\\pm}"),
  ('\178',"\\Ax{^2}"),
  ('\179',"\\Ax{^3}"),
  ('\180',"\\Ax{\\acute{\\ }}"),
  ('\181',"\\Ax{\\mu}"),
  ('\185',"\\Ax{^1}"),
  ('\186',"\\Id{\\textordmasculine}"),
  ('\187',"\\Id{\\guillemotright}"),
  ('\192',"\\Ax{\\grave{A}}"),
  ('\193',"\\Ax{\\acute{A}}"),
  ('\200',"\\Ax{\\grave{E}}"),
  ('\201',"\\Ax{\\acute{E}}"),
  ('\204',"\\Ax{\\grave{I}}"),
  ('\205',"\\Ax{\\acute{I}}"),
  ('\208',"\\Id{\\DH}"),
  ('\210',"\\Ax{\\grave{O}}"),
  ('\211',"\\Ax{\\acute{O}}"),
  ('\215',"\\Ax{\\times}"),
  ('\217',"\\Ax{\\grave{U}}"),
  ('\218',"\\Ax{\\acute{U}}"),
  ('\221',"\\Ax{\\acute{Y}}"),
  ('\222',"\\Id{\\TH}"),
  ('\224',"\\Ax{\\grave{a}}"),
  ('\225',"\\Ax{\\acute{a}}"),
  ('\232',"\\Ax{\\grave{e}}"),
  ('\233',"\\Ax{\\acute{e}}"),
  ('\236',"\\Ax{\\grave{\\Id{\\i}}}"),
  ('\237',"\\Ax{\\acute{\\Id{\\i}}}"),
  ('\240',"\\Id{\\dh}"),
  ('\242',"\\Ax{\\grave{o}}"),
  ('\243',"\\Ax{\\acute{o}}"),
  ('\247',"\\Ax{\\div}"),
  ('\249',"\\Ax{\\grave{u}}"),
  ('\250',"\\Ax{\\acute{u}}"),
  ('\253',"\\Ax{\\acute{y}}"),
  ('\254',"\\Id{\\th}")]

{- acute and grave characters don't work in a tabbing environment
   \textcent upto textbrokenbar requires \usepackage{textcomp}
    whereas \guillemot, eth, and thorn  \usepackage[T1]{fontenc}
-}
