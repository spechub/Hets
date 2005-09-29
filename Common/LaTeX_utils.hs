{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Useful functions for latex printing
-}

module Common.LaTeX_utils (module Common.LaTeX_utils,
                       module Common.LaTeX_funs,
                       hspace_latex) where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Print_AS_Annotation(splitAndPrintRAnnos)
import Common.LaTeX_AS_Annotation
import Common.Lib.Pretty
import Common.PrintLaTeX

import Common.LaTeX_funs hiding (startAnno,endAnno) 

-- | LaTeX variants 
commaT_latex,semiT_latex,crossT_latex 
    :: PrintLaTeX a => GlobalAnnos -> [a] -> Doc

commaT_latex = listSep_latex comma_latex
semiT_latex = listSep_latex semi_latex
crossT_latex = listSep_latex 
               (space_latex <> hc_sty_axiom "\\times"<> space_latex)

listSep_latex :: PrintLaTeX a => Doc -> GlobalAnnos -> [a] -> Doc
listSep_latex separator ga = fsep_latex . punctuate separator .
                             map (printLatex0 ga)


semiAnno_latex :: (PrintLaTeX a) => 
                  GlobalAnnos -> [Annoted a] -> Doc
semiAnno_latex ga l = if null l then empty else
                   (vcat $ map (pf' True)
                              (init l) ++ [pf' False (last l)])
    where pfga as = vcat $ map (printLatex0 ga) as
          pf' printSemi a_item =
              leftAF (rightAF (
                 if isEmpty laImpl then item'' else fsep_latex [item'', laImpl]))
              where (laImpl,ras) = splitAndPrintRAnnos printLatex0 
                                             printAnnotationList_Latex0 
                                             (<\+>)
                                             (latex_macro "\\`" <>) empty 
                                             ga (r_annos a_item)
                    item' = printLatex0 ga (item a_item)
                    item'' = if printSemi then item'<>semi_latex else item'
                    leftAF = if null l_annos' then id 
                                              else ($$) (pfga l_annos')
                    l_annos' = l_annos a_item
                    rightAF = if isEmpty ras then id
                                             else (\ x -> x $$ ras)

tabList_latex :: [Doc] -> [Doc]
tabList_latex [] = []
tabList_latex [x] = [startTab_latex <> x <> endTab_latex]
tabList_latex l = let h' = startTab_latex <> head l
                      l' = last l <>endTab_latex
                      rema = if null $ tail l 
                            then [] 
                            else init $ tail l 
                  in h':rema++[l']

-- Heng: case Anweisung einführen, wie in hc_sty_hetcasl_keyword
hc_sty_casl_keyword :: String -> Doc
hc_sty_casl_keyword str =
      case str of 
      "sort" -> sp_t "\\SORT"
      "sorts" -> sp_t "\\SORTS"
      "op" -> sp_t "\\OP"
      "ops" -> sp_t "\\OPS"
      "pred" -> sp_t "\\PRED"
      "preds" -> sp_t "\\PREDS"
      "type" -> sp_t "\\TYPE"
      "types" -> sp_t "\\TYPES"
      str' -> hc_sty_keyword (Just "preds") str'      
      where sp_t s = sp_text (keyword_width "preds") s

sp_hang_latex :: Doc -> Int -> Doc -> Doc
sp_hang_latex d1 n d2 = cat [d1, nest_latex n d2]

sp_between_latex :: Doc -> Doc -> Doc -> Doc
sp_between_latex lb rb p = sp_hang_latex (sp_hang_latex lb 1 p) 0 rb

sp_braces_latex :: Doc -> Doc
sp_braces_latex = 
    sp_between_latex (casl_normal_latex "\\{") (casl_normal_latex "\\}")

sp_braces_latex2 :: Doc -> Doc
sp_braces_latex2 d =
    fcat [casl_normal_latex "\\{"<>d,
          casl_normal_latex "\\}"]

sp_brackets_latex :: Doc -> Doc
sp_brackets_latex =
    sp_between_latex (casl_normal_latex "[") (casl_normal_latex "]")

simple_id_latex :: SIMPLE_ID -> Doc 
simple_id_latex = hc_sty_structid . tokStr

simple_id_indexed_latex :: SIMPLE_ID -> Doc
simple_id_indexed_latex = hc_sty_structid_indexed . tokStr
parens_tab_latex :: Doc -> Doc
parens_tab_latex = parens_latex.set_tabbed_nest_latex

-- |
-- constant document to start indentation by a LaTeX tab stop
startTab_latex :: Doc
startTab_latex = latex_macro startTab

-- |
-- constant document to end indentation by a LaTeX tab stop
endTab_latex :: Doc
endTab_latex = latex_macro endTab

-- |
-- constant document to set a LaTeX tab stop at this position
setTab_latex :: Doc
setTab_latex = latex_macro setTab

setTabWithSpaces_latex :: Int -> Doc
setTabWithSpaces_latex = latex_macro . setTabWithSpaces

-- |
-- function for nice indentation
tabbed_nest_latex :: Doc -> Doc
tabbed_nest_latex d = startTab_latex <> d <> endTab_latex

-- |
-- function for nice indentation together with starting
set_tabbed_nest_latex :: Doc -> Doc
set_tabbed_nest_latex d = setTab_latex <> tabbed_nest_latex d 

tab_nest_latex :: Int -> Doc -> Doc
tab_nest_latex i d = tabbed_nest_latex (nest_latex i d)
{- tab_nest_latex i d =
   setTabWithSpaces_latex i <> tabbed_nest_latex (nest_latex i d)
-}
tab_hang_latex :: Doc -> Int -> Doc -> Doc
tab_hang_latex d1 i d2 = sep_latex [d1, tab_nest_latex i d2]
{-tab_hang_latex d1 i d2 = 
    setTabWithSpaces_latex i 
        <> sep_latex [d1, tabbed_nest_latex (nest_latex i d2)]
-}

