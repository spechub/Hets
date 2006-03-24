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
    , semiAnno_latex
    , fromLatex
    ) where

import Common.AS_Annotation
import Common.GlobalAnnotations

import Common.PrintLaTeX
import Common.Lib.Pretty

import qualified Common.Doc as Doc

instance PrintLaTeX Annotation where
    printLatex0 ga = Doc.toLatex ga . Doc.annoDoc

printAnnotationList_Latex0 :: GlobalAnnos -> [Annotation] -> Doc
printAnnotationList_Latex0 ga = Doc.toLatex ga . Doc.printAnnotationList

fromLatex :: PrintLaTeX a => GlobalAnnos -> a -> Doc.Doc
fromLatex ga = Doc.literalDoc . printLatex0 ga

instance PrintLaTeX a => PrintLaTeX (Annoted a) where
    printLatex0 ga = Doc.toLatex ga . Doc.printAnnoted (fromLatex ga)

instance PrintLaTeX s => PrintLaTeX (Named s) where
    printLatex0 ga = printLatex0 ga . Doc.fromLabelledSen

semiAnno_latex :: PrintLaTeX a => GlobalAnnos -> [Annoted a] -> Doc
semiAnno_latex ga = Doc.toLatex ga . Doc.semiAnnos (fromLatex ga)
