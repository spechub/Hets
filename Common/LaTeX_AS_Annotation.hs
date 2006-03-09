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

import Common.Id (nullRange)
import Common.PrintLaTeX
import Common.Lib.Pretty
import Common.LaTeX_funs
import qualified Common.Doc as Doc

instance PrintLaTeX Annotation where
    printLatex0 ga = Doc.toLatex ga . Doc.annoDoc

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
