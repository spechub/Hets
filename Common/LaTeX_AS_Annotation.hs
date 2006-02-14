{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module contains all instances of PrintLaTeX for AS_Annotation.hs
-}

module Common.LaTeX_AS_Annotation
    ( printAnnotationList_Latex0
    , splitAndPrintRAnnos_latex
    , semiAnno_latex
    ) where

import Common.AS_Annotation
import Common.Print_AS_Annotation

import Common.GlobalAnnotations

import Common.Id (Id(..),splitMixToken,Token,nullRange)
import Common.PrintLaTeX
import Common.Lib.Pretty
import Common.PPUtils (printToks)
import Common.Lexer(whiteChars)
import Common.LaTeX_funs

infixl 6 <\\+>

instance PrintLaTeX Annotation where
    printLatex0 _ (Unparsed_anno aw at _) =
        case at of
                Line_anno str ->
                    case aw of
                            Comment_start ->
                                hc_sty_comment
                                ( hc_sty_small_keyword "\\%\\%"
                                  <> casl_comment_latex
                                       (escape_comment_latex str))
                            Annote_word w -> printLatexLine w $
                                             if all (`elem` whiteChars) str
                                                then empty
                                                else casl_annotation_latex
                                                     (escape_comment_latex str)
                Group_anno strs ->
                    case aw of
                    Comment_start ->
                        case strs of
                        [] -> hc_sty_comment
                              (hc_sty_small_keyword "\\%\\{" <\\+>
                                  hc_sty_small_keyword "\\}\\%")
                        [x] -> hc_sty_comment (hc_sty_small_keyword "\\%\\{" <>
                                  conv x <> hc_sty_small_keyword "\\}\\%")
                        xs -> hc_sty_comment
                                     (hc_sty_small_keyword "\\%\\{" <>
                                      latex_macro setTab <>
                                      latex_macro startTab <>
                                      vcat (map conv xs) <>
                                      hc_sty_small_keyword "\\}\\%" <>
                                      latex_macro endTab)
                        where conv  = casl_comment_latex . escape_comment_latex
                    Annote_word w -> printLatexGroup w $ vcat
                                     $ map (casl_annotation_latex
                                            . escape_latex) strs
    printLatex0 ga (Display_anno aa ab _) =
        let aa' = printSmallId_orig_latex aa
            ab' = fsep_small $ map printPair $ filter nullSnd ab
        in printLatexGroup "display" $ aa' <\\+> ab'
           where printPair (s1,s2) = la ("%" ++ lookupDisplayFormat s1)
                                     <\\+> maybe (la s2) pr_tops tops
                 tops = lookupDisplay ga DF_LATEX aa
                 la = casl_annotation_latex . escape_latex
                 pr_tops = fcat . printToks aa printAnnotationToken_latex
                 nullSnd (_,s2) = not $ null s2
                 printSmallId_orig_latex (Id toks ids _) =
                     let ids' = case ids of
                                [] -> empty
                                _  ->  ((\x -> casl_comment_latex "[" <> x
                                         <> casl_comment_latex "]")
                                        . fcat
                                        . punctuate smallComma_latex
                                        . map (printSmallId_latex ga)) ids
                         (ts,ps) = splitMixToken toks
                         pr_tops' =
                           hcat . map (printToken_latex casl_annotation_latex)
                     in pr_tops' ts <> ids' <> pr_tops' ps
    printLatex0 ga (String_anno aa ab _) =
        let aa' = printSmallId_latex ga aa
            ab' = printSmallId_latex ga ab
        in printLatexLine "string" $ aa' <> smallComma_latex <\\+> ab'
    printLatex0 ga (List_anno aa ab ac _) =
        let aa' = printSmallId_latex ga aa
            ab' = printSmallId_latex ga ab
            ac' = printSmallId_latex ga ac
        in printLatexLine "list" $ aa' <> smallComma_latex <\\+> ab'
                                  <> smallComma_latex <\\+> ac'
    printLatex0 ga (Number_anno aa _) =
        let aa' = printSmallId_latex ga aa
        in printLatexLine "number" aa'
    printLatex0 ga (Float_anno aa ab _) =
        let aa' = printSmallId_latex ga aa
            ab' = printSmallId_latex ga ab
        in printLatexLine "floating" $ aa' <> smallComma_latex <\\+> ab'
    printLatex0 ga (Prec_anno pflag ab ac _) =
        let aa' = hc_sty_axiom $ showPrecRel pflag
            p_list = (\l -> casl_comment_latex "\\{" <> l
                                <> casl_comment_latex "\\}")
                     . fsep_small
                     . punctuate smallComma_latex
                     . map (printSmallId_latex ga)
        in  printLatexGroup "prec" $ fsep_small [p_list ab, aa', p_list ac]
    printLatex0 ga (Assoc_anno as aa _) =
        printLatexGroup (case as of
                         ALeft -> "left\\_assoc"
                         ARight -> "right\\_assoc") $ fsep_small $
        punctuate smallComma_latex $
        map (printSmallId_latex ga) aa
    printLatex0 _ (Label aa _) =
        let aa' = vcat $ map (casl_annotation_latex . escape_latex) aa
        in flushright $
           hc_sty_annotation (hc_sty_small_keyword ("\\%(") <>
                              aa' <> hc_sty_small_keyword ")\\%" )
    printLatex0 _ (Semantic_anno sa  _) =
        printLatexLine (lookupSemanticAnno sa)  empty

fsep_small :: [Doc] -> Doc
fsep_small = fcat . punctuate smallSpace_latex

-- -------------------------------------------------------------------------
-- utilities
-- -------------------------------------------------------------------------
printAnnotationToken_latex :: Token -> Doc
printAnnotationToken_latex = printDisplayToken_latex casl_annotation_latex

smallSpace_latex :: Doc
smallSpace_latex = casl_comment_latex " "

smallComma_latex :: Doc
smallComma_latex = casl_comment_latex ","

(<\\+>) :: Doc -> Doc -> Doc
d1 <\\+> d2 = if isEmpty d1 then d2 else
                  if isEmpty d2 then d1 else d1 <> smallSpace_latex <> d2

printSmallId_latex :: GlobalAnnos -> Id -> Doc
printSmallId_latex ga i@(Id tops ids _) =
    let ids' = case ids of
               [] -> empty
               _  ->  ((\x -> casl_comment_latex "[" <> x
                                  <> casl_comment_latex "]")
                       . fcat
                       . punctuate smallComma_latex
                       . map (printSmallId_latex ga)) ids
        (ts,ps) = splitMixToken tops
        pr_tops = fcat . map (printToken_latex casl_annotation_latex)
    in maybe (pr_tops ts <> ids' <> pr_tops ps)
             (fcat . printToks i printAnnotationToken_latex)
             (lookupDisplay ga DF_LATEX i)

printLatexGroup :: String -> Doc -> Doc
printLatexGroup kw grp =
    hc_sty_annotation (hc_sty_small_keyword ("\\%"++kw++"(")
                       <> latex_macro setTab <> latex_macro startTab
                       <> grp<> hc_sty_small_keyword ")\\%"
                       <> latex_macro endTab)

printLatexLine :: String -> Doc -> Doc
printLatexLine kw line =
    hc_sty_annotation (if isEmpty line then kw_d else kw_d <\\+> line)
    where kw_d = hc_sty_small_keyword ("\\%"++kw)

printAnnotationList_Latex0 :: GlobalAnnos -> [Annotation] -> Doc
printAnnotationList_Latex0 ga = vcat . map (printLatex0 ga)

splitAndPrintRAnnos_latex :: GlobalAnnos -> Doc -> [Annotation] -> Doc
splitAndPrintRAnnos_latex ga i ras =
    let (la, ras') = splitAndPrintRAnnos printLatex0
            printAnnotationList_Latex0 (<\+>) flushright empty ga ras
        la' = hspace_latex "3mm" <> la
    in (if isEmpty la then i else fcat [i, la']) $$ ras'

instance PrintLaTeX a => PrintLaTeX (Annoted a) where
    printLatex0 ga (Annoted i _ las ras) =
        let r = splitAndPrintRAnnos_latex ga (printLatex0 ga i) ras
        in if null las then r else
               space_latex $+$ printAnnotationList_Latex0 ga las $+$ r

instance PrintLaTeX s => PrintLaTeX (Named s) where
    printLatex0 ga (NamedSen{senName = label, sentence = s}) =
        printLatex0 ga s <\+> printLatex0 ga (Label [label] nullRange)

semiAnno_latex :: PrintLaTeX a => GlobalAnnos -> [Annoted a] -> Doc
semiAnno_latex ga l = if null l then empty else
                   vcat (map (pf' True)
                              (init l) ++ [pf' False $ last l])
    where pf' printSemi (Annoted i _ las ras) =
              printAnnotationList_Latex0 ga las $+$
              splitAndPrintRAnnos_latex ga item'' ras
              where item' = printLatex0 ga i
                    item'' = if printSemi then item' <> semi_latex else item'
